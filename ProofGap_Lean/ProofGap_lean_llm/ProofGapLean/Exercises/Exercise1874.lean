import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Set Real

namespace ProofGap.Exercise1874

noncomputable section

def domain : Set ℝ := Set.Ioo (-2) (-1)

def integrand (x : ℝ) : ℝ :=
  1 / ((x + 1) * (x + 2) ^ 2 * (x + 3) ^ 3)

def partialFractions (x : ℝ) : ℝ :=
  1 / (8 * (x + 1)) + 2 / (x + 2) - 1 / (x + 2) ^ 2 -
    17 / (8 * (x + 3)) - 5 / (4 * (x + 3) ^ 2) -
    1 / (2 * (x + 3) ^ 3)

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {G | DifferentiableOn ℝ G domain ∧ ∀ x ∈ domain, deriv G x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {G | ∃ K : ℝ, ∀ x ∈ domain, G x = p x + K}

def expandedPrimitive (x : ℝ) : ℝ :=
  (1 / 8 : ℝ) * Real.log |x + 1| + 2 * Real.log |x + 2| +
    1 / (x + 2) - (17 / 8 : ℝ) * Real.log |x + 3| +
    5 / (4 * (x + 3)) + 1 / (4 * (x + 3) ^ 2)

def combinedPrimitive (x : ℝ) : ℝ :=
  (1 / 8 : ℝ) *
      Real.log |((x + 1) * (x + 2) ^ 16) / (x + 3) ^ 17| +
    (9 * x ^ 2 + 50 * x + 68) / (4 * (x + 2) * (x + 3) ^ 2)

theorem gap1 :
    ∃ A B C D E F : ℝ, ∀ x,
      x ≠ -1 → x ≠ -2 → x ≠ -3 →
      integrand x = A / (x + 1) + B / (x + 2) + C / (x + 2) ^ 2 +
        D / (x + 3) + E / (x + 3) ^ 2 + F / (x + 3) ^ 3 := by
  refine ⟨1 / 8, 2, -1, -(17 / 8), -(5 / 4), -(1 / 2), ?_⟩
  intro x hx1 hx2 hx3
  have h1 : x + 1 ≠ 0 := by
    intro h
    apply hx1
    linarith
  have h2 : x + 2 ≠ 0 := by
    intro h
    apply hx2
    linarith
  have h3 : x + 3 ≠ 0 := by
    intro h
    apply hx3
    linarith
  unfold integrand
  field_simp [h1, h2, h3]
  ring

theorem gap2 :
    ∃ A B C D E F : ℝ, ∀ x, 1 =
      A * (x + 2) ^ 2 * (x + 3) ^ 3 +
        B * (x + 1) * (x + 2) * (x + 3) ^ 3 +
        C * (x + 1) * (x + 3) ^ 3 +
        D * (x + 1) * (x + 2) ^ 2 * (x + 3) ^ 2 +
        E * (x + 1) * (x + 2) ^ 2 * (x + 3) +
        F * (x + 1) * (x + 2) ^ 2 := by
  refine ⟨1 / 8, 2, -1, -(17 / 8), -(5 / 4), -(1 / 2), ?_⟩
  intro x
  ring

theorem gap3 : ∃ A : ℝ, 1 = 8 * A := by
  exact ⟨1 / 8, by norm_num⟩

theorem gap4 : ∃ A : ℝ, A = (1 / 8 : ℝ) := by
  exact ⟨1 / 8, rfl⟩

theorem gap5 : ∃ C : ℝ, 1 = -C := by
  exact ⟨-1, by norm_num⟩

theorem gap6 : ∃ C : ℝ, C = -1 := by
  exact ⟨-1, rfl⟩

theorem gap7 : ∃ F : ℝ, 1 = -2 * F := by
  exact ⟨-(1 / 2), by norm_num⟩

theorem gap8 : ∃ F : ℝ, F = -(1 / 2 : ℝ) := by
  exact ⟨-(1 / 2), rfl⟩

theorem gap9 : ∃ A B D : ℝ, A + B + D = 0 := by
  exact ⟨0, 0, 0, by norm_num⟩

theorem gap10 : ∃ A B C D E : ℝ, 13 * A + 12 * B + C + 11 * D + E = 0 := by
  exact ⟨0, 0, 0, 0, 0, by norm_num⟩

theorem gap11 :
    ∃ A B C D E F : ℝ, 67 * A + 56 * B + 10 * C + 47 * D + 8 * E + F = 0 := by
  exact ⟨0, 0, 0, 0, 0, 0, by norm_num⟩

theorem gap12 : ∃ B : ℝ, B = 2 := by
  exact ⟨2, rfl⟩

theorem gap13 : ∃ D : ℝ, D = -(17 / 8 : ℝ) := by
  exact ⟨-(17 / 8), rfl⟩

theorem gap14 : ∃ E : ℝ, E = -(5 / 4 : ℝ) := by
  exact ⟨-(5 / 4), rfl⟩

private theorem domain_ne {x : ℝ} (hx : x ∈ domain) :
    x + 1 ≠ 0 ∧ x + 2 ≠ 0 ∧ x + 3 ≠ 0 := by
  have hx' : -2 < x ∧ x < -1 := hx
  constructor
  · linarith
  constructor <;> linarith

private theorem integrand_eq_partialFractions {x : ℝ} (hx : x ∈ domain) :
    integrand x = partialFractions x := by
  obtain ⟨h1, h2, h3⟩ := domain_ne hx
  unfold integrand partialFractions
  field_simp [h1, h2, h3]
  ring

private theorem log_abs_add_hasDerivAt (x c : ℝ) (h : x + c ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.log |y + c|) (1 / (x + c)) x := by
  have hraw :=
    (Real.hasDerivAt_log h).comp x ((hasDerivAt_id x).add_const c)
  simpa only [Function.comp_def, Real.log_abs, id_eq, mul_one, one_div] using hraw

private theorem inv_add_hasDerivAt (x c : ℝ) (h : x + c ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 / (y + c)) (-1 / (x + c) ^ 2) x := by
  simpa [one_div] using ((hasDerivAt_id x).add_const c).inv h

private theorem expandedPrimitive_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt expandedPrimitive (partialFractions x) x := by
  obtain ⟨h1, h2, h3⟩ := domain_ne hx
  have hl1 := log_abs_add_hasDerivAt x 1 h1
  have hl2 := log_abs_add_hasDerivAt x 2 h2
  have hl3 := log_abs_add_hasDerivAt x 3 h3
  have hi2 := inv_add_hasDerivAt x 2 h2
  have hi3 := inv_add_hasDerivAt x 3 h3
  have h1' : 1 + x ≠ 0 := by simpa [add_comm] using h1
  have h2' : 2 + x ≠ 0 := by simpa [add_comm] using h2
  have h3' : 3 + x ≠ 0 := by simpa [add_comm] using h3
  have hi3sq :
      HasDerivAt (fun y : ℝ => (1 / (y + 3)) ^ 2)
        (-2 / (x + 3) ^ 3) x := by
    convert hi3.pow 2 using 1
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp [h3, h3']
  let alt : ℝ → ℝ := fun y =>
    (1 / 8 : ℝ) * Real.log |y + 1| + 2 * Real.log |y + 2| +
      1 / (y + 2) + (-(17 / 8 : ℝ)) * Real.log |y + 3| +
      (5 / 4 : ℝ) * (1 / (y + 3)) +
      (1 / 4 : ℝ) * (1 / (y + 3)) ^ 2
  have hraw : HasDerivAt alt
      (1 / 8 * (1 / (x + 1)) + 2 * (1 / (x + 2)) +
        -1 / (x + 2) ^ 2 + -(17 / 8) * (1 / (x + 3)) +
        5 / 4 * (-1 / (x + 3) ^ 2) +
        1 / 4 * (-2 / (x + 3) ^ 3)) x := by
    dsimp [alt]
    exact
    (((((hl1.const_mul (1 / 8 : ℝ)).add (hl2.const_mul 2)).add hi2).add
      (hl3.const_mul (-(17 / 8 : ℝ)))).add
      (hi3.const_mul (5 / 4 : ℝ))).add
      (hi3sq.const_mul (1 / 4 : ℝ))
  have heq : expandedPrimitive =ᶠ[nhds x] alt := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    obtain ⟨hy1, hy2, hy3⟩ := domain_ne hy
    unfold expandedPrimitive alt
    field_simp [hy1, hy2, hy3]
    ring
  have halt := hraw.congr_of_eventuallyEq heq
  unfold partialFractions
  convert halt using 1
  field_simp [h1, h2, h3, h1', h2', h3']
  field_simp [h1, h2, h3, h1', h2', h3']
  ring

theorem gap15 :
    antiderivatives integrand = antiderivatives partialFractions := by
  ext G
  simp only [antiderivatives, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hG, hderiv⟩
    exact ⟨hG, fun x hx => (hderiv x hx).trans (integrand_eq_partialFractions hx)⟩
  · rintro ⟨hG, hderiv⟩
    exact ⟨hG, fun x hx => (hderiv x hx).trans (integrand_eq_partialFractions hx).symm⟩

theorem gap16 :
    antiderivatives integrand = primitiveFamily expandedPrimitive := by
  rw [gap15]
  ext G
  simp only [antiderivatives, primitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hGdiff, hGderiv⟩
    let H : ℝ → ℝ := fun x => G x - expandedPrimitive x
    have hHzero : ∀ x ∈ domain, HasDerivAt H 0 x := by
      intro x hx
      have hGat : DifferentiableAt ℝ G x :=
        (hGdiff x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
      have hGder : HasDerivAt G (partialFractions x) x := by
        simpa only [hGderiv x hx] using hGat.hasDerivAt
      simpa [H] using hGder.sub (expandedPrimitive_hasDerivAt hx)
    have hHdiff : DifferentiableOn ℝ H domain := by
      intro x hx
      exact (hHzero x hx).differentiableAt.differentiableWithinAt
    have hHderiv : ∀ x ∈ domain, deriv H x = 0 := by
      intro x hx
      exact (hHzero x hx).deriv
    refine ⟨G (-(3 / 2)) - expandedPrimitive (-(3 / 2)), ?_⟩
    intro x hx
    have hx₀ : (-(3 / 2) : ℝ) ∈ domain := by norm_num [domain]
    have hc : H x = H (-(3 / 2)) :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hHdiff hHderiv hx hx₀
    dsimp [H] at hc
    linarith
  · rintro ⟨K, hGK⟩
    have hGat : ∀ x ∈ domain, HasDerivAt G (partialFractions x) x := by
      intro x hx
      have hsum := (expandedPrimitive_hasDerivAt hx).add_const K
      have hevent : G =ᶠ[nhds x] fun y => expandedPrimitive y + K := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
        exact hGK y hy
      exact hsum.congr_of_eventuallyEq hevent
    constructor
    · intro x hx
      exact (hGat x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hGat x hx).deriv

private theorem expanded_eq_combined {x : ℝ} (hx : x ∈ domain) :
    expandedPrimitive x = combinedPrimitive x := by
  obtain ⟨h1, h2, h3⟩ := domain_ne hx
  have hlog :
      Real.log |((x + 1) * (x + 2) ^ 16) / (x + 3) ^ 17| =
        Real.log |x + 1| + 16 * Real.log |x + 2| -
          17 * Real.log |x + 3| := by
    simp only [Real.log_abs]
    rw [Real.log_div (mul_ne_zero h1 (pow_ne_zero 16 h2))
      (pow_ne_zero 17 h3)]
    rw [Real.log_mul h1 (pow_ne_zero 16 h2)]
    rw [Real.log_pow, Real.log_pow]
    norm_num
  unfold expandedPrimitive combinedPrimitive
  rw [hlog]
  field_simp [h2, h3]
  ring

theorem gap17 :
    antiderivatives integrand = primitiveFamily combinedPrimitive := by
  rw [gap16]
  ext G
  simp only [primitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨K, hGK⟩
    exact ⟨K, fun x hx => (hGK x hx).trans
      (congrArg (fun z => z + K) (expanded_eq_combined hx))⟩
  · rintro ⟨K, hGK⟩
    exact ⟨K, fun x hx => (hGK x hx).trans
      (congrArg (fun z => z + K) (expanded_eq_combined hx).symm)⟩

end

end ProofGap.Exercise1874
