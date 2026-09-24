import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1847

noncomputable section

def domain : Set ℝ := Set.Ioo (-1 - Real.sqrt 2) (-1 + Real.sqrt 2)

def integrand (x : ℝ) : ℝ := 1 / Real.sqrt (1 - 2 * x - x ^ 2)

def shiftedIntegrand (x : ℝ) : ℝ :=
  1 / Real.sqrt (2 - (x + 1) ^ 2)

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

def primitive (x : ℝ) : ℝ := Real.arcsin ((x + 1) / Real.sqrt 2)

private theorem primitive_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt primitive (shiftedIntegrand x) x := by
  unfold domain at hx
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hlow : -(Real.sqrt 2) < x + 1 := by
    nlinarith [hx.1]
  have hupp : x + 1 < Real.sqrt 2 := by
    nlinarith [hx.2]
  have hu_low : -1 < (x + 1) / Real.sqrt 2 := by
    apply (lt_div_iff₀ hsqrt2pos).2
    nlinarith
  have hu_upp : (x + 1) / Real.sqrt 2 < 1 := by
    apply (div_lt_iff₀ hsqrt2pos).2
    nlinarith
  have hinside : 0 < 2 - (x + 1) ^ 2 := by
    nlinarith
  have huinside : 0 < 1 - ((x + 1) / Real.sqrt 2) ^ 2 := by
    rw [div_pow, hsqrt2sq]
    nlinarith
  have hradical :
      Real.sqrt (1 - ((x + 1) / Real.sqrt 2) ^ 2) * Real.sqrt 2 =
        Real.sqrt (2 - (x + 1) ^ 2) := by
    rw [← Real.sqrt_mul (le_of_lt huinside)]
    congr 1
    rw [div_pow, hsqrt2sq]
    ring
  have hcoeff :
      (1 / Real.sqrt (1 - ((x + 1) / Real.sqrt 2) ^ 2)) *
          (1 / Real.sqrt 2) =
        1 / Real.sqrt (2 - (x + 1) ^ 2) := by
    rw [← hradical]
    field_simp [ne_of_gt (Real.sqrt_pos.2 huinside), ne_of_gt hsqrt2pos]
  have harg :
      HasDerivAt (fun y : ℝ => (y + 1) / Real.sqrt 2)
        (1 / Real.sqrt 2) x := by
    simpa using ((hasDerivAt_id x).add_const 1).div_const (Real.sqrt 2)
  have hchain :
      HasDerivAt primitive
        ((1 / Real.sqrt (1 - ((x + 1) / Real.sqrt 2) ^ 2)) *
          (1 / Real.sqrt 2)) x := by
    simpa [primitive] using
      (Real.hasDerivAt_arcsin (ne_of_gt hu_low) (ne_of_lt hu_upp)).comp x harg
  convert hchain using 1
  exact hcoeff.symm

theorem gap1 : antiderivatives integrand = antiderivatives shiftedIntegrand := by
  apply congrArg antiderivatives
  funext x
  unfold integrand shiftedIntegrand
  apply congrArg (fun t : ℝ => 1 / Real.sqrt t)
  ring

theorem gap2 :
    antiderivatives shiftedIntegrand = primitiveFamily primitive := by
  ext F
  change
    (DifferentiableOn ℝ F domain ∧
      ∀ x ∈ domain, deriv F x = shiftedIntegrand x) ↔
    ∃ C : ℝ, ∀ x ∈ domain, F x = primitive x + C
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hbase : (-1 : ℝ) ∈ domain := by
      unfold domain
      constructor <;> nlinarith
    have hHhas :
        ∀ x ∈ domain,
          HasDerivAt (fun y : ℝ => F y - primitive y) 0 x := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
      simpa [hFderiv x hx] using
        hFat.hasDerivAt.sub (primitive_hasDerivAt hx)
    have hHdiff :
        DifferentiableOn ℝ (fun y : ℝ => F y - primitive y) domain := by
      intro x hx
      exact (hHhas x hx).differentiableAt.differentiableWithinAt
    have hHzero :
        ∀ x ∈ domain, deriv (fun y : ℝ => F y - primitive y) x = 0 := by
      intro x hx
      exact (hHhas x hx).deriv
    have hconst :
        ∀ x ∈ domain,
          F x - primitive x = F (-1) - primitive (-1) := by
      intro x hx
      exact isOpen_Ioo.is_const_of_deriv_eq_zero
        isPreconnected_Ioo hHdiff hHzero hx hbase
    refine ⟨F (-1) - primitive (-1), ?_⟩
    intro x hx
    have := hconst x hx
    linarith
  · rintro ⟨C, hFC⟩
    have hpDiff :
        DifferentiableOn ℝ (fun y : ℝ => primitive y + C) domain := by
      intro x hx
      exact ((primitive_hasDerivAt hx).add_const C).differentiableAt.differentiableWithinAt
    constructor
    · exact hpDiff.congr (fun x hx => hFC x hx)
    · intro x hx
      have hev : F =ᶠ[nhds x] (fun y : ℝ => primitive y + C) :=
        Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx) (fun y hy => hFC y hy)
      calc
        deriv F x = deriv (fun y : ℝ => primitive y + C) x := hev.deriv_eq
        _ = shiftedIntegrand x := ((primitive_hasDerivAt hx).add_const C).deriv

theorem gap3 : antiderivatives integrand = primitiveFamily primitive := by
  calc
    antiderivatives integrand = antiderivatives shiftedIntegrand := gap1
    _ = primitiveFamily primitive := gap2

end

end ProofGap.Exercise1847
