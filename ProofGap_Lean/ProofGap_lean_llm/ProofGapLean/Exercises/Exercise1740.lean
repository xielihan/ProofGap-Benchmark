import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1740

noncomputable section

def original (a b x : ℝ) : ℝ := 1 / ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2))
def partialFractions (a b x : ℝ) : ℝ :=
  (1 / (a ^ 2 - b ^ 2)) * (1 / (x ^ 2 + b ^ 2) - 1 / (x ^ 2 + a ^ 2))
def primitive (a b x : ℝ) : ℝ :=
  (1 / (a ^ 2 - b ^ 2)) *
    ((1 / b) * Real.arctan (x / b) - (1 / a) * Real.arctan (x / a))
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem original_eq_partialFractions
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : |a| ≠ |b|) :
    original a b = partialFractions a b := by
  funext x
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have hxa : x ^ 2 + a ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have hxb : x ^ 2 + b ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have hab2 : a ^ 2 - b ^ 2 ≠ 0 := by
    intro h
    apply hab
    have hs : a ^ 2 = b ^ 2 := sub_eq_zero.mp h
    nlinarith [sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b]
  unfold original partialFractions
  field_simp [hxa, hxb, hab2]
  <;> ring

private theorem hasDerivAt_scaled_arctan
    (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (1 / c) * Real.arctan (y / c))
      (1 / (x ^ 2 + c ^ 2)) x := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hxc : x ^ 2 + c ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have hone : 1 + (x / c) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (x / c)]
  convert (((Real.hasDerivAt_arctan (x / c)).comp x
    ((hasDerivAt_id x).div_const c)).const_mul (1 / c)) using 1 <;>
    field_simp [hc, hxc, hone] <;> ring

private theorem hasDerivAt_primitive
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (x : ℝ) :
    HasDerivAt (primitive a b) (partialFractions a b x) x := by
  unfold primitive partialFractions
  exact ((hasDerivAt_scaled_arctan b hb x).sub
    (hasDerivAt_scaled_arctan a ha x)).const_mul (1 / (a ^ 2 - b ^ 2))

private theorem eq_at_zero_of_deriv_eq_zero
    (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hderiv : ∀ x, deriv f x = 0) :
    ∀ x, f x = f 0 := by
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · obtain ⟨c, _, hslope⟩ :=
      exists_deriv_eq_slope f hx hf.continuous.continuousOn hf.differentiableOn
    rw [hderiv c] at hslope
    have hden : 0 - x ≠ 0 := by linarith
    field_simp [hden] at hslope
    linarith
  · simpa [hx]
  · obtain ⟨c, _, hslope⟩ :=
      exists_deriv_eq_slope f hx hf.continuous.continuousOn hf.differentiableOn
    rw [hderiv c] at hslope
    have hden : x - 0 ≠ 0 := by linarith
    field_simp [hden] at hslope
    linarith

private theorem antiderivatives_eq_primitiveFamily
    (g p : ℝ → ℝ) (hp : Differentiable ℝ p)
    (hderiv : ∀ x, deriv p x = g x) :
    Antiderivatives g = PrimitiveFamily p := by
  ext F
  constructor
  · rintro ⟨hF, hFderiv⟩
    have hd : Differentiable ℝ (fun x => F x - p x) := hF.sub hp
    have hz : ∀ x, deriv (fun y => F y - p y) x = 0 := by
      intro x
      simpa [hFderiv x, hderiv x] using
        (((hF x).hasDerivAt).sub ((hp x).hasDerivAt)).deriv
    refine ⟨F 0 - p 0, ?_⟩
    intro x
    have hx := eq_at_zero_of_deriv_eq_zero (fun y => F y - p y) hd hz x
    linarith [hx]
  · rintro ⟨C, hC⟩
    have hFC : F = fun x => p x + C := funext hC
    subst F
    constructor
    · exact hp.add (differentiable_const C)
    · intro x
      simpa [hderiv x] using (((hp x).hasDerivAt).add_const C).deriv

theorem gap1 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : |a| ≠ |b|) :
    Antiderivatives (original a b) = Antiderivatives (partialFractions a b) := by
  rw [original_eq_partialFractions a b ha hb hab]

theorem gap2 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : |a| ≠ |b|) :
    Antiderivatives (partialFractions a b) = PrimitiveFamily (primitive a b) := by
  apply antiderivatives_eq_primitiveFamily
  · intro x
    exact (hasDerivAt_primitive a b ha hb x).differentiableAt
  · intro x
    exact (hasDerivAt_primitive a b ha hb x).deriv

theorem gap3 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : |a| ≠ |b|) :
    Antiderivatives (original a b) = PrimitiveFamily (primitive a b) := by
  exact (gap1 a b ha hb hab).trans (gap2 a b ha hb hab)

end
end ProofGap.Exercise1740
