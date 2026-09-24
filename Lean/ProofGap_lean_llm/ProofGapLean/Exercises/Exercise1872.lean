import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1872

noncomputable section

def domain : Set ℝ := Set.Ioo (-1) 1

def integrand (x : ℝ) : ℝ := (x ^ 2 + 1) / ((x + 1) ^ 2 * (x - 1))

def partialFractions (x : ℝ) : ℝ :=
  1 / (2 * (x + 1)) - 1 / (x + 1) ^ 2 + 1 / (2 * (x - 1))

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

def primitive (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log |x ^ 2 - 1| + 1 / (x + 1)

private theorem integrand_eq_partialFractions (x : ℝ) (hxneg : x ≠ -1)
    (hxpos : x ≠ 1) : integrand x = partialFractions x := by
  have hplus : x + 1 ≠ 0 := by
    intro h
    apply hxneg
    linarith
  have hminus : x - 1 ≠ 0 := by
    intro h
    apply hxpos
    linarith
  unfold integrand partialFractions
  field_simp [hplus, hminus]
  <;> ring

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  rcases hx with ⟨hxlow, hxhigh⟩
  have hplus : x + 1 ≠ 0 := by
    intro h
    linarith
  have hminus : x - 1 ≠ 0 := by
    intro h
    linarith
  have hquad : x ^ 2 - 1 ≠ 0 := by
    have hleft : 0 < x + 1 := by linarith
    have hright : 0 < 1 - x := by linarith
    have hprod : 0 < (x + 1) * (1 - x) := mul_pos hleft hright
    intro h
    nlinarith
  have hpoly :
      HasDerivAt (fun y : ℝ => y ^ 2 - 1) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).sub_const 1 using 1 <;> norm_num <;> ring
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (y ^ 2 - 1))
        ((2 * x) / (x ^ 2 - 1)) x :=
    hpoly.log hquad
  have hden : HasDerivAt (fun y : ℝ => y + 1) 1 x :=
    (hasDerivAt_id x).add_const 1
  have hinv :
      HasDerivAt (fun y : ℝ => 1 / (y + 1)) (-1 / (x + 1) ^ 2) x := by
    simpa [one_div] using hden.inv hplus
  have hsum :
      HasDerivAt
        (fun y : ℝ => (1 / 2 : ℝ) * Real.log (y ^ 2 - 1) + 1 / (y + 1))
        ((1 / 2 : ℝ) * ((2 * x) / (x ^ 2 - 1)) +
          (-1 / (x + 1) ^ 2)) x :=
    (hlog.const_mul (1 / 2 : ℝ)).add hinv
  have hfun :
      (fun y : ℝ => (1 / 2 : ℝ) * Real.log (y ^ 2 - 1) + 1 / (y + 1)) =
        primitive := by
    funext y
    simp [primitive, Real.log_abs]
  have halg :
      (1 / 2 : ℝ) * ((2 * x) / (x ^ 2 - 1)) +
          (-1 / (x + 1) ^ 2) = integrand x := by
    unfold integrand
    field_simp [hplus, hminus, hquad]
    <;> ring
  rw [← hfun, ← halg]
  exact hsum

theorem gap1 :
    ∃ A B C : ℝ, ∀ x, x ≠ -1 → x ≠ 1 →
      integrand x = A / (x + 1) + B / (x + 1) ^ 2 + C / (x - 1) := by
  refine ⟨(1 / 2 : ℝ), -1, (1 / 2 : ℝ), ?_⟩
  intro x hxneg hxpos
  have hplus : x + 1 ≠ 0 := by
    intro h
    apply hxneg
    linarith
  have hminus : x - 1 ≠ 0 := by
    intro h
    apply hxpos
    linarith
  rw [integrand_eq_partialFractions x hxneg hxpos]
  unfold partialFractions
  field_simp [hplus, hminus]
  <;> ring

theorem gap2 :
    ∃ A B C : ℝ, ∀ x,
      x ^ 2 + 1 = A * (x + 1) * (x - 1) +
        B * (x - 1) + C * (x + 1) ^ 2 := by
  refine ⟨(1 / 2 : ℝ), -1, (1 / 2 : ℝ), ?_⟩
  intro x
  ring

theorem gap3 : ∃ B : ℝ, 2 = -2 * B := by
  refine ⟨(-1 : ℝ), ?_⟩
  norm_num

theorem gap4 : ∃ B : ℝ, B = -1 := by
  exact ⟨(-1 : ℝ), rfl⟩

theorem gap5 : ∃ C : ℝ, 2 = 4 * C := by
  refine ⟨(1 / 2 : ℝ), ?_⟩
  norm_num

theorem gap6 : ∃ C : ℝ, C = (1 / 2 : ℝ) := by
  exact ⟨(1 / 2 : ℝ), rfl⟩

theorem gap7 : ∃ A C : ℝ, A + C = 1 := by
  refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), ?_⟩
  norm_num

theorem gap8 : ∃ A : ℝ, A = (1 / 2 : ℝ) := by
  exact ⟨(1 / 2 : ℝ), rfl⟩

theorem gap9 :
    antiderivatives integrand = antiderivatives partialFractions := by
  apply Set.ext
  intro F
  simp only [antiderivatives, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    have hxneg : x ≠ -1 := by
      intro h
      rw [h] at hx
      exact (lt_irrefl (-1)) hx.1
    have hxpos : x ≠ 1 := by
      intro h
      rw [h] at hx
      exact (lt_irrefl 1) hx.2
    rw [← integrand_eq_partialFractions x hxneg hxpos]
    exact hderiv x hx
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    have hxneg : x ≠ -1 := by
      intro h
      rw [h] at hx
      exact (lt_irrefl (-1)) hx.1
    have hxpos : x ≠ 1 := by
      intro h
      rw [h] at hx
      exact (lt_irrefl 1) hx.2
    rw [integrand_eq_partialFractions x hxneg hxpos]
    exact hderiv x hx

theorem gap10 : antiderivatives integrand = primitiveFamily primitive := by
  apply Set.ext
  intro F
  simp only [antiderivatives, primitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hpDiff : DifferentiableOn ℝ primitive domain := by
      intro x hx
      exact (primitive_hasDerivAt x hx).differentiableAt.differentiableWithinAt
    have hsubDiff :
        DifferentiableOn ℝ (fun x => F x - primitive x) domain :=
      hFdiff.sub hpDiff
    have hsubDeriv :
        ∀ x ∈ domain, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
      have hFhas : HasDerivAt F (integrand x) x := by
        simpa [hFderiv x hx] using hFat.hasDerivAt
      simpa using (hFhas.sub (primitive_hasDerivAt x hx)).deriv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hzero : (0 : ℝ) ∈ domain := by
      constructor <;> norm_num
    have heq :=
      isOpen_Ioo.is_const_of_deriv_eq_zero
        (isPreconnected_Ioo : IsPreconnected (Set.Ioo (-1 : ℝ) 1))
        hsubDiff hsubDeriv hx hzero
    linarith
  · rintro ⟨C, hFC⟩
    have hbaseDiff :
        DifferentiableOn ℝ (fun y => primitive y + C) domain := by
      intro x hx
      exact ((primitive_hasDerivAt x hx).add_const C).differentiableAt.differentiableWithinAt
    refine ⟨hbaseDiff.congr (fun x hx => hFC x hx), ?_⟩
    intro x hx
    have hevent : ∀ᶠ y in nhds x, F y = primitive y + C :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx) (by
        intro y hy
        exact hFC y hy)
    calc
      deriv F x = deriv (fun y => primitive y + C) x :=
        Filter.EventuallyEq.deriv_eq hevent
      _ = integrand x := ((primitive_hasDerivAt x hx).add_const C).deriv

end

end ProofGap.Exercise1872
