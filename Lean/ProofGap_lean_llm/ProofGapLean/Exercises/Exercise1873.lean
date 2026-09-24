import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1873

noncomputable section

def domain : Set ℝ := Set.Ioo 1 2

def integrand (x : ℝ) : ℝ := (x / (x ^ 2 - 3 * x + 2)) ^ 2

def factoredIntegrand (x : ℝ) : ℝ :=
  x ^ 2 / ((x - 1) ^ 2 * (x - 2) ^ 2)

def partialFractions (x : ℝ) : ℝ :=
  4 / (x - 1) + 1 / (x - 1) ^ 2 -
    4 / (x - 2) + 4 / (x - 2) ^ 2

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

def expandedPrimitive (x : ℝ) : ℝ :=
  4 * Real.log |x - 1| - 1 / (x - 1) -
    4 * Real.log |x - 2| - 4 / (x - 2)

def combinedPrimitive (x : ℝ) : ℝ :=
  4 * Real.log |(x - 1) / (x - 2)| -
    (5 * x - 6) / (x ^ 2 - 3 * x + 2)

private theorem integrand_eq_partialFractions (x : ℝ) (hx : x ∈ domain) :
    integrand x = partialFractions x := by
  have hx1 : x ≠ 1 := ne_of_gt hx.1
  have hx2 : x ≠ 2 := ne_of_lt hx.2
  have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have h2 : x - 2 ≠ 0 := sub_ne_zero.mpr hx2
  have hi : integrand x = factoredIntegrand x := by
    unfold integrand factoredIntegrand
    rw [show x ^ 2 - 3 * x + 2 = (x - 1) * (x - 2) by ring,
      div_pow, mul_pow]
  rw [hi]
  unfold factoredIntegrand partialFractions
  field_simp [h1, h2] <;> ring

private theorem expanded_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt expandedPrimitive (partialFractions x) x := by
  have hx1 : x ≠ 1 := ne_of_gt hx.1
  have hx2 : x ≠ 2 := ne_of_lt hx.2
  have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have h2 : x - 2 ≠ 0 := sub_ne_zero.mpr hx2
  have hs1 : HasDerivAt (fun y : ℝ => y - 1) 1 x :=
    (hasDerivAt_id x).sub_const 1
  have hs2 : HasDerivAt (fun y : ℝ => y - 2) 1 x :=
    (hasDerivAt_id x).sub_const 2
  have hl1 : HasDerivAt (fun y : ℝ => Real.log |y - 1|) (1 / (x - 1)) x := by
    simpa [Function.comp_def, Real.log_abs, one_div] using
      (Real.hasDerivAt_log h1).comp x hs1
  have hl2 : HasDerivAt (fun y : ℝ => Real.log |y - 2|) (1 / (x - 2)) x := by
    simpa [Function.comp_def, Real.log_abs, one_div] using
      (Real.hasDerivAt_log h2).comp x hs2
  have h :=
    (((hl1.const_mul 4).sub
      ((hasDerivAt_const x (1 : ℝ)).div hs1 h1)).sub
      (hl2.const_mul 4)).sub
      ((hasDerivAt_const x (4 : ℝ)).div hs2 h2)
  unfold expandedPrimitive partialFractions
  convert h using 1 <;> field_simp [h1, h2] <;> ring

private theorem expanded_eq_combined (x : ℝ) (hx : x ∈ domain) :
    expandedPrimitive x = combinedPrimitive x := by
  have hx1 : x ≠ 1 := ne_of_gt hx.1
  have hx2 : x ≠ 2 := ne_of_lt hx.2
  have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have h2 : x - 2 ≠ 0 := sub_ne_zero.mpr hx2
  have ha1 : |x - 1| ≠ 0 := abs_ne_zero.mpr h1
  have ha2 : |x - 2| ≠ 0 := abs_ne_zero.mpr h2
  have hrat :
      1 / (x - 1) + 4 / (x - 2) =
        (5 * x - 6) / (x ^ 2 - 3 * x + 2) := by
    rw [show x ^ 2 - 3 * x + 2 = (x - 1) * (x - 2) by ring]
    field_simp [h1, h2] <;> ring
  calc
    expandedPrimitive x =
        4 * (Real.log |x - 1| - Real.log |x - 2|) -
          (1 / (x - 1) + 4 / (x - 2)) := by
      unfold expandedPrimitive
      ring
    _ = 4 * (Real.log |x - 1| - Real.log |x - 2|) -
          (5 * x - 6) / (x ^ 2 - 3 * x + 2) := by rw [hrat]
    _ = combinedPrimitive x := by
      unfold combinedPrimitive
      rw [abs_div, Real.log_div ha1 ha2]

theorem gap1 :
    ∀ x, x ≠ 1 → x ≠ 2 → integrand x = factoredIntegrand x := by
  intro x _ _
  unfold integrand factoredIntegrand
  rw [show x ^ 2 - 3 * x + 2 = (x - 1) * (x - 2) by ring,
    div_pow, mul_pow]

theorem gap2 :
    ∃ A B C D : ℝ, ∀ x, x ≠ 1 → x ≠ 2 →
      factoredIntegrand x =
        A / (x - 1) + B / (x - 1) ^ 2 +
          C / (x - 2) + D / (x - 2) ^ 2 := by
  refine ⟨4, 1, -4, 4, ?_⟩
  intro x hx1 hx2
  have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have h2 : x - 2 ≠ 0 := sub_ne_zero.mpr hx2
  unfold factoredIntegrand
  field_simp [h1, h2] <;> ring

theorem gap3 :
    ∃ A B C D : ℝ, ∀ x, x ^ 2 =
      A * (x - 1) * (x - 2) ^ 2 + B * (x - 2) ^ 2 +
        C * (x - 2) * (x - 1) ^ 2 + D * (x - 1) ^ 2 := by
  refine ⟨4, 1, -4, 4, ?_⟩
  intro x
  ring

theorem gap4 : ∃ B : ℝ, B = 1 := by
  exact ⟨1, rfl⟩

theorem gap5 : ∃ D : ℝ, D = 4 := by
  exact ⟨4, rfl⟩

theorem gap6 : ∃ A C : ℝ, A + C = 0 := by
  exact ⟨0, 0, by norm_num⟩

theorem gap7 : ∃ A B C D : ℝ, -5 * A + B - 4 * C + D = 1 := by
  refine ⟨0, 1, 0, 0, ?_⟩
  norm_num

theorem gap8 : ∃ A : ℝ, A = 4 := by
  exact ⟨4, rfl⟩

theorem gap9 : ∃ C : ℝ, C = -4 := by
  exact ⟨-4, rfl⟩

theorem gap10 :
    antiderivatives integrand = antiderivatives partialFractions := by
  apply Set.ext
  intro F
  change
    (DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = integrand x) ↔
      (DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = partialFractions x)
  constructor
  · rintro ⟨hF, hder⟩
    refine ⟨hF, ?_⟩
    intro x hx
    exact (hder x hx).trans (integrand_eq_partialFractions x hx)
  · rintro ⟨hF, hder⟩
    refine ⟨hF, ?_⟩
    intro x hx
    exact (hder x hx).trans (integrand_eq_partialFractions x hx).symm

theorem gap11 :
    antiderivatives integrand = primitiveFamily expandedPrimitive := by
  apply Set.ext
  intro F
  change
    (DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = integrand x) ↔
      (∃ C : ℝ, ∀ x ∈ domain, F x = expandedPrimitive x + C)
  have hopen : IsOpen domain := by
    simpa [domain] using (isOpen_Ioo : IsOpen (Set.Ioo (1 : ℝ) 2))
  constructor
  · rintro ⟨hF, hder⟩
    have hdiff :
        DifferentiableOn ℝ (fun y => F y - expandedPrimitive y) domain := by
      intro x hx
      exact (hF x hx).sub
        (expanded_hasDerivAt x hx).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ domain,
        deriv (fun y => F y - expandedPrimitive y) x = 0 := by
      intro x hx
      have hFa : DifferentiableAt ℝ F x :=
        (hF x hx).differentiableAt (hopen.mem_nhds hx)
      have heq : deriv F x = partialFractions x :=
        (hder x hx).trans (integrand_eq_partialFractions x hx)
      have hz : HasDerivAt (fun y => F y - expandedPrimitive y) 0 x := by
        convert hFa.hasDerivAt.sub (expanded_hasDerivAt x hx) using 1 <;>
          simp [heq]
      exact hz.deriv
    have hdiffIoo :
        DifferentiableOn ℝ (fun y => F y - expandedPrimitive y)
          (Set.Ioo (1 : ℝ) 2) := by
      simpa [domain] using hdiff
    have hzeroIoo :
        Set.EqOn (deriv (fun y => F y - expandedPrimitive y)) 0
          (Set.Ioo (1 : ℝ) 2) := by
      intro x hx
      apply hzero x
      simpa [domain] using hx
    let b : ℝ := 3 / 2
    have hb : b ∈ domain := by
      dsimp [b, domain]
      constructor <;> norm_num
    refine ⟨F b - expandedPrimitive b, ?_⟩
    intro x hx
    have hc :
        F x - expandedPrimitive x = F b - expandedPrimitive b :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hdiffIoo hzeroIoo (x := x) (y := b)
        (by simpa [domain] using hx)
        (by simpa [domain] using hb)
    linarith
  · rintro ⟨C, hC⟩
    have hhas : ∀ x ∈ domain, HasDerivAt F (partialFractions x) x := by
      intro x hx
      have hwithin :
          HasDerivWithinAt F (partialFractions x) domain x := by
        apply ((expanded_hasDerivAt x hx).add_const C).hasDerivWithinAt.congr
        · intro y hy
          exact hC y hy
        · exact hC x hx
      exact hwithin.hasDerivAt (hopen.mem_nhds hx)
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hhas x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hhas x hx).deriv.trans (integrand_eq_partialFractions x hx).symm

theorem gap12 :
    antiderivatives integrand = primitiveFamily combinedPrimitive := by
  rw [gap11]
  apply Set.ext
  intro F
  change
    (∃ C : ℝ, ∀ x ∈ domain, F x = expandedPrimitive x + C) ↔
      (∃ C : ℝ, ∀ x ∈ domain, F x = combinedPrimitive x + C)
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hC x hx, expanded_eq_combined x hx]
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hC x hx, expanded_eq_combined x hx]

end

end ProofGap.Exercise1873
