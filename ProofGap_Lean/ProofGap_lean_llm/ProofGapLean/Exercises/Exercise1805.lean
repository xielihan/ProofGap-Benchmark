import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise1805

noncomputable section

def branch : Set ℝ := Set.Ioo (-1 : ℝ) 1
def integrand (x : ℝ) := x ^ 2 * Real.arccos x
def scaledDerivativeIntegrand (x : ℝ) :=
  (1 / 3 : ℝ) * Real.arccos x * deriv (fun t : ℝ => t ^ 3) x
def residual₁ (x : ℝ) := x ^ 3 / Real.sqrt (1 - x ^ 2)
def substitution (x : ℝ) := 1 - x ^ 2
def rawResidual (x : ℝ) :=
  x ^ 2 / Real.sqrt (1 - x ^ 2) * deriv substitution x
def rewrittenRawResidual (x : ℝ) :=
  (1 / Real.sqrt (1 - x ^ 2) - Real.sqrt (1 - x ^ 2)) *
    deriv substitution x
def boundary (x : ℝ) := (1 / 3 : ℝ) * x ^ 3 * Real.arccos x
def primitive₁ (x : ℝ) :=
  boundary x - (1 / 3 : ℝ) * Real.sqrt (1 - x ^ 2) +
    (1 / 9 : ℝ) * Real.rpow (1 - x ^ 2) (3 / 2 : ℝ)
def primitive₂ (x : ℝ) :=
  boundary x - (x ^ 2 + 2) / 9 * Real.sqrt (1 - x ^ 2)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ByPartsFamily (b : ℝ → ℝ) (c : ℝ) (r : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn r, ∀ x ∈ branch, F x = b x + c * G x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem substitution_pos {x : ℝ} (hx : x ∈ branch) :
    0 < 1 - x ^ 2 := by
  have hp : 0 < (x + 1) * (1 - x) :=
    mul_pos (by linarith [hx.1]) (by linarith [hx.2])
  nlinarith

private theorem hasDerivAt_substitution (x : ℝ) :
    HasDerivAt substitution (-2 * x) x := by
  simpa [substitution] using
    (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)

private theorem scaledDerivativeIntegrand_eq_integrand (x : ℝ) :
    scaledDerivativeIntegrand x = integrand x := by
  have hder : deriv (fun t : ℝ => t ^ 3) x = 3 * x ^ 2 := by
    convert ((hasDerivAt_id x).pow 3).deriv using 1 <;> norm_num <;> ring
  simp only [scaledDerivativeIntegrand, integrand]
  rw [hder]
  ring

private theorem hasDerivAt_boundary (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt boundary
      (integrand x - (1 / 3 : ℝ) * residual₁ x) x := by
  have hcub := ((hasDerivAt_id x).pow 3).const_mul (1 / 3 : ℝ)
  have harccos := Real.hasDerivAt_arccos
    (x := x) (by linarith [hx.1]) (by linarith [hx.2])
  convert hcub.mul harccos using 1 <;>
    simp [integrand, residual₁] <;> ring

private theorem rawResidual_eq_residual (x : ℝ) :
    rawResidual x = -2 * residual₁ x := by
  have hder := (hasDerivAt_substitution x).deriv
  simp only [rawResidual, residual₁]
  rw [hder]
  ring

private theorem rawResidual_eq_rewritten (x : ℝ) (hx : x ∈ branch) :
    rawResidual x = rewrittenRawResidual x := by
  have hu : 0 < 1 - x ^ 2 := substitution_pos hx
  have hspos : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hu
  have hsne : Real.sqrt (1 - x ^ 2) ≠ 0 := ne_of_gt hspos
  have hsq : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hu)
  have hfrac :
      x ^ 2 / Real.sqrt (1 - x ^ 2) =
        1 / Real.sqrt (1 - x ^ 2) - Real.sqrt (1 - x ^ 2) := by
    field_simp [hsne]
    nlinarith [hsq]
  simp only [rawResidual, rewrittenRawResidual]
  rw [hfrac]

private theorem residualRawFamily :
    ByPartsFamily boundary (1 / 3) residual₁ =
      ByPartsFamily boundary (-1 / 6) rawResidual := by
  ext F
  simp only [ByPartsFamily, AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, hG, hEq⟩
    refine ⟨fun y => -2 * G y, ?_, ?_⟩
    · intro x hx
      simpa only [rawResidual_eq_residual x] using
        (hG x hx).const_mul (-2 : ℝ)
    · intro x hx
      rw [hEq x hx]
      ring
  · rintro ⟨G, hG, hEq⟩
    refine ⟨fun y => (-1 / 2 : ℝ) * G y, ?_, ?_⟩
    · intro x hx
      have hd := (hG x hx).const_mul (-1 / 2 : ℝ)
      convert hd using 1
      rw [rawResidual_eq_residual x]
      ring
    · intro x hx
      rw [hEq x hx]
      ring

private theorem antiderivativesOn_eq_primitiveFamily
    (p : ℝ → ℝ)
    (hp : ∀ x ∈ branch, HasDerivAt p (integrand x) x) :
    AntiderivativesOn integrand = PrimitiveFamily p := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨F 0 - p 0, ?_⟩
    intro x hx
    let g : ℝ → ℝ := fun y => F y - p y
    have hg : ∀ y ∈ branch, HasDerivAt g 0 y := by
      intro y hy
      simpa [g] using (hF y hy).sub (hp y hy)
    have hgdiff : DifferentiableOn ℝ g branch := by
      intro y hy
      exact (hg y hy).differentiableAt.differentiableWithinAt
    have hgzero : ∀ y ∈ branch, deriv g y = 0 := by
      intro y hy
      exact (hg y hy).deriv
    have hpre : IsPreconnected branch := by
      simpa [branch] using
        (convex_Ioo (-1 : ℝ) 1).isPreconnected
    have hconst : ∀ y ∈ branch, ∀ z ∈ branch, g y = g z := by
      intro y hy z hz
      exact
        (isOpen_Ioo.is_const_of_deriv_eq_zero hpre hgdiff hgzero) hy hz
    have hzero_mem : (0 : ℝ) ∈ branch := by
      norm_num [branch]
    have hgx : g x = g 0 := hconst x hx 0 hzero_mem
    dsimp [g] at hgx
    linarith
  · rintro ⟨C, hFC⟩
    intro x hx
    have heq : Filter.EventuallyEq (nhds x) F (fun y => p y + C) :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx) (fun y hy => hFC y hy)
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq

private theorem hasDerivAt_primitive₂ (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive₂ (integrand x) x := by
  have hu : 0 < 1 - x ^ 2 := substitution_pos hx
  have hspos : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hu
  have hsne : Real.sqrt (1 - x ^ 2) ≠ 0 := ne_of_gt hspos
  have hsq : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hu)
  have hsqrt :
      HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
        (-x / Real.sqrt (1 - x ^ 2)) x := by
    have hs0 := (Real.hasDerivAt_sqrt hu.ne').comp x
      (hasDerivAt_substitution x)
    convert hs0 using 1 <;> field_simp [hsne]
  have hcoeff :
      HasDerivAt (fun y : ℝ => (y ^ 2 + 2) / 9) (2 * x / 9) x := by
    convert (((hasDerivAt_id x).pow 2).add_const 2).const_mul
      (1 / 9 : ℝ) using 1 <;> norm_num <;> ring
  have hval :
      (integrand x - (1 / 3 : ℝ) * residual₁ x) -
          ((2 * x / 9) * Real.sqrt (1 - x ^ 2) +
            ((x ^ 2 + 2) / 9) * (-x / Real.sqrt (1 - x ^ 2))) =
        integrand x := by
    simp only [residual₁]
    field_simp [hsne]
    rw [hsq]
    ring
  change HasDerivAt
    (fun y : ℝ => boundary y - (y ^ 2 + 2) / 9 * Real.sqrt (1 - y ^ 2))
    (integrand x) x
  have hd := (hasDerivAt_boundary x hx).sub (hcoeff.mul hsqrt)
  rw [hval] at hd
  exact hd

private theorem primitive₁_eq_primitive₂ (x : ℝ) (hx : x ∈ branch) :
    primitive₁ x = primitive₂ x := by
  have hu : 0 < 1 - x ^ 2 := substitution_pos hx
  have hadd :
      Real.rpow (1 - x ^ 2) (1 + 1 / 2) =
        Real.rpow (1 - x ^ 2) 1 * Real.rpow (1 - x ^ 2) (1 / 2) := by
    simpa only using
      (Real.rpow_add hu (1 : ℝ) (1 / 2 : ℝ))
  have hone : Real.rpow (1 - x ^ 2) (1 : ℝ) = 1 - x ^ 2 := by
    simp
  have hhalf :
      Real.rpow (1 - x ^ 2) (1 / 2 : ℝ) = Real.sqrt (1 - x ^ 2) := by
    exact (Real.sqrt_eq_rpow (1 - x ^ 2)).symm
  have hrpow :
      Real.rpow (1 - x ^ 2) (3 / 2 : ℝ) =
        (1 - x ^ 2) * Real.sqrt (1 - x ^ 2) := by
    calc
      Real.rpow (1 - x ^ 2) (3 / 2 : ℝ) =
          Real.rpow (1 - x ^ 2) (1 + 1 / 2) := by norm_num
      _ = Real.rpow (1 - x ^ 2) 1 *
          Real.rpow (1 - x ^ 2) (1 / 2) := hadd
      _ = (1 - x ^ 2) * Real.sqrt (1 - x ^ 2) := by
        rw [hone, hhalf]
  rw [primitive₁, primitive₂, hrpow]
  ring

private theorem primitiveFamily_congr {p q : ℝ → ℝ}
    (hpq : ∀ x ∈ branch, p x = q x) :
    PrimitiveFamily p = PrimitiveFamily q := by
  ext F
  simp only [PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hF x hx, hpq x hx]
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hF x hx, ← hpq x hx]

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn scaledDerivativeIntegrand := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    simpa only [scaledDerivativeIntegrand_eq_integrand x] using h x hx
  · intro h x hx
    simpa only [scaledDerivativeIntegrand_eq_integrand x] using h x hx
theorem gap2 :
    AntiderivativesOn scaledDerivativeIntegrand =
      ByPartsFamily boundary (1 / 3) residual₁ := by
  ext F
  simp only [AntiderivativesOn, ByPartsFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => 3 * (F y - boundary y), ?_, ?_⟩
    · intro x hx
      have hd := ((hF x hx).sub (hasDerivAt_boundary x hx)).const_mul 3
      convert hd using 1
      rw [scaledDerivativeIntegrand_eq_integrand x]
      ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hEq⟩
    intro x hx
    have hd :
        HasDerivAt (fun y => boundary y + (1 / 3 : ℝ) * G y)
          (scaledDerivativeIntegrand x) x := by
      convert (hasDerivAt_boundary x hx).add
        ((hG x hx).const_mul (1 / 3 : ℝ)) using 1
      rw [scaledDerivativeIntegrand_eq_integrand x]
      ring
    have heq : Filter.EventuallyEq (nhds x) F
        (fun y => boundary y + (1 / 3 : ℝ) * G y) :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx) (fun y hy => hEq y hy)
    exact hd.congr_of_eventuallyEq heq
theorem gap3 :
    AntiderivativesOn integrand =
      ByPartsFamily boundary (1 / 3) residual₁ := by
  exact gap1.trans gap2
theorem gap4 :
    AntiderivativesOn integrand =
      ByPartsFamily boundary (-1 / 6) rawResidual := by
  exact gap3.trans residualRawFamily
theorem gap5 :
    ByPartsFamily boundary (-1 / 6) rawResidual =
      ByPartsFamily boundary (-1 / 6) rewrittenRawResidual := by
  ext F
  simp only [ByPartsFamily, AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, hG, hEq⟩
    refine ⟨G, ?_, hEq⟩
    intro x hx
    simpa only [rawResidual_eq_rewritten x hx] using hG x hx
  · rintro ⟨G, hG, hEq⟩
    refine ⟨G, ?_, hEq⟩
    intro x hx
    simpa only [rawResidual_eq_rewritten x hx] using hG x hx
theorem gap6 :
    AntiderivativesOn integrand =
      ByPartsFamily boundary (-1 / 6) rewrittenRawResidual := by
  exact gap4.trans gap5
theorem gap7 :
    AntiderivativesOn integrand = PrimitiveFamily primitive₁ := by
  calc
    AntiderivativesOn integrand = PrimitiveFamily primitive₂ :=
      antiderivativesOn_eq_primitiveFamily primitive₂ hasDerivAt_primitive₂
    _ = PrimitiveFamily primitive₁ :=
      (primitiveFamily_congr primitive₁_eq_primitive₂).symm
theorem gap8 :
    PrimitiveFamily primitive₁ = PrimitiveFamily primitive₂ := by
  exact primitiveFamily_congr primitive₁_eq_primitive₂
theorem gap9 :
    AntiderivativesOn integrand = PrimitiveFamily primitive₂ := by
  exact gap7.trans gap8

end
end ProofGap.Exercise1805
