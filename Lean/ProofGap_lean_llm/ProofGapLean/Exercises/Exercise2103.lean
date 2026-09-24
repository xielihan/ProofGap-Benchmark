import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2103
noncomputable section

def domain : Set ℝ := Set.Ioo (-1) 1
def logSum (x : ℝ) :=
  Real.log (Real.sqrt (1 - x) + Real.sqrt (1 + x))
def integrand (x : ℝ) := logSum x
def residual (x : ℝ) := (1 - Real.sqrt (1 - x ^ 2)) / Real.sqrt (1 - x ^ 2)
def primitive (x : ℝ) :=
  x * logSum x + (1 / 2 : ℝ) * Real.arcsin x - (1 / 2 : ℝ) * x

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ domain, HasDerivAt F (f x) x}
def FirstReduction :=
  {F : ℝ → ℝ | ∃ A ∈ Family residual,
    ∀ x ∈ domain, F x = x * logSum x + (1 / 2 : ℝ) * A x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

theorem gap1 : Family integrand = FirstReduction := by
  ext F
  constructor
  · intro hF
    let A : ℝ → ℝ := fun x => 2 * (F x - x * logSum x)
    refine ⟨A, ?_, ?_⟩
    · intro x hx
      have hx1 : 0 < 1 - x := by linarith [hx.2]
      have hx2 : 0 < 1 + x := by linarith [hx.1]
      have hs1 : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.2 hx1
      have hs2 : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.2 hx2
      have hsum : Real.sqrt (1 - x) + Real.sqrt (1 + x) ≠ 0 :=
        ne_of_gt (add_pos hs1 hs2)
      have hne1 : 1 - x ≠ 0 := ne_of_gt hx1
      have hne2 : 1 + x ≠ 0 := ne_of_gt hx2
      have hsder1 : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y))
          (-1 / (2 * Real.sqrt (1 - x))) x := by
        convert (Real.hasDerivAt_sqrt (x := 1 - x) hne1).comp x
          ((hasDerivAt_const x 1).sub (hasDerivAt_id x)) using 1 <;> ring
      have hsder2 : HasDerivAt (fun y : ℝ => Real.sqrt (1 + y))
          (1 / (2 * Real.sqrt (1 + x))) x := by
        convert (Real.hasDerivAt_sqrt (x := 1 + x) hne2).comp x
          ((hasDerivAt_const x 1).add (hasDerivAt_id x)) using 1 <;> ring
      have hlog : HasDerivAt logSum
          ((-1 / (2 * Real.sqrt (1 - x)) + 1 / (2 * Real.sqrt (1 + x))) /
            (Real.sqrt (1 - x) + Real.sqrt (1 + x))) x := by
        unfold logSum
        simpa [div_eq_mul_inv, mul_comm] using
          ((Real.hasDerivAt_log hsum).comp x (hsder1.add hsder2))
      have hprod := (hasDerivAt_id x).mul hlog
      have hA := (hF x hx).sub hprod
      convert (hA.const_mul 2) using 1
      have hs1sq : (Real.sqrt (1 - x)) ^ 2 = 1 - x :=
        Real.sq_sqrt (le_of_lt hx1)
      have hs2sq : (Real.sqrt (1 + x)) ^ 2 = 1 + x :=
        Real.sq_sqrt (le_of_lt hx2)
      have hquad : 0 < 1 - x ^ 2 := by nlinarith
      have hsprod : Real.sqrt (1 - x) * Real.sqrt (1 + x) =
          Real.sqrt (1 - x ^ 2) := by
        rw [← Real.sqrt_mul (le_of_lt hx1)]
        congr 1
        ring
      have hsqne : Real.sqrt (1 - x ^ 2) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 hquad)
      unfold integrand residual
      dsimp [A]
      rw [← hsprod]
      field_simp
      nlinarith
    · intro x hx
      dsimp [A]
      ring
  · rintro ⟨A, hA, hF⟩
    intro x hx
    have hx1 : 0 < 1 - x := by linarith [hx.2]
    have hx2 : 0 < 1 + x := by linarith [hx.1]
    have hs1 : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.2 hx1
    have hs2 : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.2 hx2
    have hsum : Real.sqrt (1 - x) + Real.sqrt (1 + x) ≠ 0 :=
      ne_of_gt (add_pos hs1 hs2)
    have hne1 : 1 - x ≠ 0 := ne_of_gt hx1
    have hne2 : 1 + x ≠ 0 := ne_of_gt hx2
    have hsder1 : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y))
        (-1 / (2 * Real.sqrt (1 - x))) x := by
      convert (Real.hasDerivAt_sqrt (x := 1 - x) hne1).comp x
        ((hasDerivAt_const x 1).sub (hasDerivAt_id x)) using 1 <;> ring
    have hsder2 : HasDerivAt (fun y : ℝ => Real.sqrt (1 + y))
        (1 / (2 * Real.sqrt (1 + x))) x := by
      convert (Real.hasDerivAt_sqrt (x := 1 + x) hne2).comp x
        ((hasDerivAt_const x 1).add (hasDerivAt_id x)) using 1 <;> ring
    have hlog : HasDerivAt logSum
        ((-1 / (2 * Real.sqrt (1 - x)) + 1 / (2 * Real.sqrt (1 + x))) /
          (Real.sqrt (1 - x) + Real.sqrt (1 + x))) x := by
      unfold logSum
      simpa [div_eq_mul_inv, mul_comm] using
        ((Real.hasDerivAt_log hsum).comp x (hsder1.add hsder2))
    have hprod := (hasDerivAt_id x).mul hlog
    have hs1sq : (Real.sqrt (1 - x)) ^ 2 = 1 - x :=
      Real.sq_sqrt (le_of_lt hx1)
    have hs2sq : (Real.sqrt (1 + x)) ^ 2 = 1 + x :=
      Real.sq_sqrt (le_of_lt hx2)
    have hquad : 0 < 1 - x ^ 2 := by nlinarith
    have hsprod : Real.sqrt (1 - x) * Real.sqrt (1 + x) =
        Real.sqrt (1 - x ^ 2) := by
      rw [← Real.sqrt_mul (le_of_lt hx1)]
      congr 1
      ring
    have hsqne : Real.sqrt (1 - x ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hquad)
    have hder : integrand x =
        (logSum x + x * ((-1 / (2 * Real.sqrt (1 - x)) +
          1 / (2 * Real.sqrt (1 + x))) /
          (Real.sqrt (1 - x) + Real.sqrt (1 + x)))) +
          (1 / 2 : ℝ) * residual x := by
      unfold integrand residual
      rw [← hsprod]
      field_simp
      nlinarith
    have htotal : HasDerivAt
        (fun y => y * logSum y + (1 / 2 : ℝ) * A y) (integrand x) x := by
      simpa [id_eq, hder] using
        (hprod.add ((hA x hx).const_mul (1 / 2 : ℝ)))
    have heq : F =ᶠ[nhds x]
        (fun y => y * logSum y + (1 / 2 : ℝ) * A y) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hF y hy
    exact htotal.congr_of_eventuallyEq heq
theorem gap2 : Family integrand = Translates primitive := by
  rw [gap1]
  ext F
  constructor
  · rintro ⟨A, hA, hF⟩
    have hprimA : ∀ x ∈ domain,
        HasDerivAt (fun y : ℝ => Real.arcsin y - y) (residual x) x := by
      intro x hx
      have hquad : 0 < 1 - x ^ 2 := by
        rcases hx with ⟨hx0, hx1⟩
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]
      have hsne : Real.sqrt (1 - x ^ 2) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 hquad)
      have harc := Real.hasDerivAt_arcsin (ne_of_gt hx.1) (ne_of_lt hx.2)
      convert harc.sub (hasDerivAt_id x) using 1
      unfold residual
      field_simp
    have hconst : ∀ x ∈ domain,
        A x - (Real.arcsin x - x) = A 0 - (Real.arcsin 0 - 0) := by
      intro x hx
      have hzero : (0 : ℝ) ∈ domain := by
        constructor <;> norm_num [domain]
      have hdiff : DifferentiableOn ℝ
          (fun y => A y - (Real.arcsin y - y)) domain := by
        intro y hy
        exact ((hA y hy).sub (hprimA y hy)).differentiableAt.differentiableWithinAt
      have hder : ∀ y ∈ domain,
          deriv (fun z => A z - (Real.arcsin z - z)) y = 0 := by
        intro y hy
        have hz : HasDerivAt (fun z => A z - (Real.arcsin z - z)) 0 y := by
          simpa using ((hA y hy).sub (hprimA y hy))
        exact hz.deriv
      exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hdiff hder hx hzero
    refine ⟨(1 / 2 : ℝ) * (A 0 - (Real.arcsin 0 - 0)), ?_⟩
    intro x hx
    rw [hF x hx]
    have hc := hconst x hx
    unfold primitive
    linarith
  · rintro ⟨C, hF⟩
    let A : ℝ → ℝ := fun x => Real.arcsin x - x + 2 * C
    refine ⟨A, ?_, ?_⟩
    · intro x hx
      have hquad : 0 < 1 - x ^ 2 := by
        rcases hx with ⟨hx0, hx1⟩
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]
      have harc := Real.hasDerivAt_arcsin (ne_of_gt hx.1) (ne_of_lt hx.2)
      convert (harc.sub (hasDerivAt_id x)).add_const (2 * C) using 1
      unfold residual
      have hsne : Real.sqrt (1 - x ^ 2) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 hquad)
      field_simp
    · intro x hx
      rw [hF x hx]
      unfold primitive
      dsimp [A]
      ring

end
end ProofGap.Exercise2103
