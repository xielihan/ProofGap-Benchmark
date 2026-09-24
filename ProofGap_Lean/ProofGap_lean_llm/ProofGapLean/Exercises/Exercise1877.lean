import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1877

noncomputable section

def domain : Set ℝ := Set.Ioi (-1)

def integrand (x : ℝ) : ℝ := 1 / ((x + 1) * (x ^ 2 + 1))

def partialFractions (x : ℝ) : ℝ :=
  1 / (2 * (x + 1)) - (x - 1) / (2 * (x ^ 2 + 1))

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

def expandedPrimitive (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log |x + 1| -
    (1 / 4 : ℝ) * Real.log (x ^ 2 + 1) +
    (1 / 2 : ℝ) * Real.arctan x

def combinedPrimitive (x : ℝ) : ℝ :=
  (1 / 4 : ℝ) * Real.log ((x + 1) ^ 2 / (x ^ 2 + 1)) +
    (1 / 2 : ℝ) * Real.arctan x

private theorem domain_isOpen : IsOpen domain := by
  simpa [domain] using (isOpen_Ioi : IsOpen (Set.Ioi (-1 : ℝ)))

private theorem domain_preconnected : IsPreconnected domain := by
  simpa [domain] using (isPreconnected_Ioi : IsPreconnected (Set.Ioi (-1 : ℝ)))

private theorem zero_mem_domain : (0 : ℝ) ∈ domain := by
  norm_num [domain]

private theorem domain_ne_neg_one {x : ℝ} (hx : x ∈ domain) : x ≠ -1 := by
  simp only [domain, Set.mem_Ioi] at hx
  linarith

private theorem integrand_eq_partialFractions {x : ℝ} (hx : x ≠ -1) :
    integrand x = partialFractions x := by
  have hlin : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hquad : x ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg x]
  unfold integrand partialFractions
  field_simp [hlin, hquad]
  ring

private theorem expandedPrimitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt expandedPrimitive (integrand x) x := by
  have hxpos : 0 < x + 1 := by
    simp only [domain, Set.mem_Ioi] at hx
    linarith
  have hqpos : 0 < x ^ 2 + 1 := by positivity
  have hlog1 : HasDerivAt (fun y : ℝ => Real.log (y + 1)) (1 / (x + 1)) x := by
    simpa [one_div, Function.comp_def] using
      (Real.hasDerivAt_log (ne_of_gt hxpos)).comp x ((hasDerivAt_id x).add_const 1)
  have hinner : HasDerivAt (fun y : ℝ => y ^ 2 + 1) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).add_const 1 using 1 <;> norm_num <;> ring
  have hlogq :
      HasDerivAt (fun y : ℝ => Real.log (y ^ 2 + 1)) (2 * x / (x ^ 2 + 1)) x := by
    simpa [div_eq_mul_inv, Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_log (ne_of_gt hqpos)).comp x hinner
  have harctan : HasDerivAt Real.arctan (1 / (x ^ 2 + 1)) x := by
    simpa [add_comm] using Real.hasDerivAt_arctan x
  have hmain :=
    ((hlog1.const_mul (1 / 2 : ℝ)).sub (hlogq.const_mul (1 / 4 : ℝ))).add
      (harctan.const_mul (1 / 2 : ℝ))
  have hnear : ∀ᶠ y in nhds x, y ∈ domain := domain_isOpen.mem_nhds hx
  have heq :
      expandedPrimitive =ᶠ[nhds x]
        ((fun y : ℝ => (1 / 2 : ℝ) * Real.log (y + 1)) -
          (fun y : ℝ => (1 / 4 : ℝ) * Real.log (y ^ 2 + 1)) +
          (fun y : ℝ => (1 / 2 : ℝ) * Real.arctan y)) := by
    apply hnear.mono
    intro y hy
    have hypos : 0 < y + 1 := by
      simp only [domain, Set.mem_Ioi] at hy
      linarith
    simp only [Pi.add_apply, Pi.sub_apply, expandedPrimitive, abs_of_pos hypos]
  have hpf : HasDerivAt expandedPrimitive (partialFractions x) x := by
    convert hmain.congr_of_eventuallyEq heq using 1
    unfold partialFractions
    field_simp [ne_of_gt hxpos, ne_of_gt hqpos]
    ring
  rw [integrand_eq_partialFractions (domain_ne_neg_one hx)]
  exact hpf

private theorem expandedPrimitive_eq_combinedPrimitive {x : ℝ} (hx : x ∈ domain) :
    expandedPrimitive x = combinedPrimitive x := by
  have hxpos : 0 < x + 1 := by
    simp only [domain, Set.mem_Ioi] at hx
    linarith
  have hqpos : 0 < x ^ 2 + 1 := by positivity
  unfold expandedPrimitive combinedPrimitive
  rw [abs_of_pos hxpos]
  rw [Real.log_div (pow_ne_zero 2 (ne_of_gt hxpos)) (ne_of_gt hqpos)]
  rw [Real.log_pow]
  ring

theorem gap1 :
    ∃ A B C : ℝ, ∀ x, x ≠ -1 →
      integrand x = A / (x + 1) + (B * x + C) / (x ^ 2 + 1) := by
  refine ⟨(1 / 2 : ℝ), -(1 / 2 : ℝ), (1 / 2 : ℝ), ?_⟩
  intro x hx
  rw [integrand_eq_partialFractions hx]
  unfold partialFractions
  have hq : x ^ 2 + 1 ≠ 0 := by nlinarith [sq_nonneg x]
  field_simp [hq]
  ring

theorem gap2 :
    ∃ A B C : ℝ, ∀ x,
      1 = A * (x ^ 2 + 1) + (B * x + C) * (x + 1) := by
  refine ⟨(1 / 2 : ℝ), -(1 / 2 : ℝ), (1 / 2 : ℝ), ?_⟩
  intro x
  ring

theorem gap3 : ∃ A B : ℝ, A + B = 0 := by
  exact ⟨0, 0, by norm_num⟩

theorem gap4 : ∃ B C : ℝ, B + C = 0 := by
  exact ⟨0, 0, by norm_num⟩

theorem gap5 : ∃ A C : ℝ, A + C = 1 := by
  exact ⟨1, 0, by norm_num⟩

theorem gap6 : ∃ A : ℝ, A = (1 / 2 : ℝ) := by
  exact ⟨(1 / 2 : ℝ), rfl⟩

theorem gap7 : ∃ B : ℝ, B = -(1 / 2 : ℝ) := by
  exact ⟨-(1 / 2 : ℝ), rfl⟩

theorem gap8 : ∃ C : ℝ, C = (1 / 2 : ℝ) := by
  exact ⟨(1 / 2 : ℝ), rfl⟩

theorem gap9 :
    antiderivatives integrand = antiderivatives partialFractions := by
  ext F
  simp only [antiderivatives, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [← integrand_eq_partialFractions (domain_ne_neg_one hx)]
    exact hderiv x hx
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [integrand_eq_partialFractions (domain_ne_neg_one hx)]
    exact hderiv x hx

theorem gap10 :
    antiderivatives integrand = primitiveFamily expandedPrimitive := by
  ext F
  simp only [antiderivatives, primitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    have hp : DifferentiableOn ℝ expandedPrimitive domain := by
      intro x hx
      exact (expandedPrimitive_hasDerivAt x hx).differentiableAt.differentiableWithinAt
    have hdiff : DifferentiableOn ℝ (fun x => F x - expandedPrimitive x) domain :=
      hF.sub hp
    have hzero : ∀ x ∈ domain, deriv (fun y => F y - expandedPrimitive y) x = 0 := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hF x hx).differentiableAt (domain_isOpen.mem_nhds hx)
      have hpat : DifferentiableAt ℝ expandedPrimitive x :=
        (expandedPrimitive_hasDerivAt x hx).differentiableAt
      change deriv (F - expandedPrimitive) x = 0
      rw [deriv_sub hFat hpat, hderiv x hx,
        (expandedPrimitive_hasDerivAt x hx).deriv]
      ring
    refine ⟨F 0 - expandedPrimitive 0, ?_⟩
    intro x hx
    have heq :=
      domain_isOpen.is_const_of_deriv_eq_zero domain_preconnected hdiff hzero
        hx zero_mem_domain
    linarith
  · rintro ⟨C, hFC⟩
    have hFx : ∀ x ∈ domain, HasDerivAt F (integrand x) x := by
      intro x hx
      have hpC : HasDerivAt (fun y => expandedPrimitive y + C) (integrand x) x :=
        (expandedPrimitive_hasDerivAt x hx).add_const C
      have hnear : ∀ᶠ y in nhds x, y ∈ domain := domain_isOpen.mem_nhds hx
      have heq : F =ᶠ[nhds x] (fun y => expandedPrimitive y + C) :=
        hnear.mono fun y hy => hFC y hy
      exact hpC.congr_of_eventuallyEq heq
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hFx x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hFx x hx).deriv

theorem gap11 :
    antiderivatives integrand = primitiveFamily combinedPrimitive := by
  rw [gap10]
  ext F
  simp only [primitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [← expandedPrimitive_eq_combinedPrimitive hx]
    exact hF x hx
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [expandedPrimitive_eq_combinedPrimitive hx]
    exact hF x hx

end

end ProofGap.Exercise1877
