import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1889

noncomputable section

def q₁ (x : ℝ) : ℝ := x ^ 2 + 2 * x + 2
def q₂ (x : ℝ) : ℝ := x ^ 2 + x + 1 / 2
def integrand (x : ℝ) : ℝ := x ^ 2 / (q₁ x * q₂ x)
def primitive (x : ℝ) : ℝ :=
  (2 / 5 : ℝ) * Real.log (q₁ x / q₂ x) +
    (8 / 5 : ℝ) * Real.arctan (x + 1) -
    (2 / 5 : ℝ) * Real.arctan (2 * x + 1)
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}
def CoeffIdentity (A B C D : ℝ) : Prop :=
  ∀ x, x ^ 2 =
    (A * x + B) * (x ^ 2 + x + 1 / 2) +
      (C * x + D) * (x ^ 2 + 2 * x + 2)

private theorem coefficientRelations (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    A + C = 0 ∧
      A + B + 2 * C + D = 1 ∧
      A / 2 + B + 2 * C + 2 * D = 0 ∧
      B / 2 + 2 * D = 0 := by
  unfold CoeffIdentity at h
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  norm_num at h0 h1 hm1 h2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

private theorem quadraticDenominators_ne_zero (x : ℝ) :
    q₁ x ≠ 0 ∧ q₂ x ≠ 0 := by
  constructor
  · unfold q₁
    nlinarith [sq_nonneg (x + 1)]
  · unfold q₂
    nlinarith [sq_nonneg (x + 1 / 2)]

theorem gap1 :
    ∃ A B C D : ℝ, CoeffIdentity A B C D := by
  refine ⟨(4 / 5 : ℝ), (12 / 5 : ℝ), -(4 / 5 : ℝ), -(3 / 5 : ℝ), ?_⟩
  unfold CoeffIdentity
  intro x
  ring

theorem gap2 (A B C D x : ℝ) (h : CoeffIdentity A B C D) :
    x ^ 2 =
      (A * x + B) * (x ^ 2 + x + 1 / 2) +
        (C * x + D) * (x ^ 2 + 2 * x + 2) := by
  exact h x

theorem gap3 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    A + C = 0 := by
  exact (coefficientRelations A B C D h).1

theorem gap4 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    A + B + 2 * C + D = 1 := by
  exact (coefficientRelations A B C D h).2.1

theorem gap5 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    A / 2 + B + 2 * C + 2 * D = 0 := by
  exact (coefficientRelations A B C D h).2.2.1

theorem gap6 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    B / 2 + 2 * D = 0 := by
  exact (coefficientRelations A B C D h).2.2.2

theorem gap7 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    A = 4 / 5 := by
  rcases coefficientRelations A B C D h with ⟨h₃, h₄, h₅, h₆⟩
  linarith

theorem gap8 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    B = 12 / 5 := by
  rcases coefficientRelations A B C D h with ⟨h₃, h₄, h₅, h₆⟩
  linarith

theorem gap9 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    C = -(4 / 5 : ℝ) := by
  rcases coefficientRelations A B C D h with ⟨h₃, h₄, h₅, h₆⟩
  linarith

theorem gap10 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    D = -(3 / 5 : ℝ) := by
  rcases coefficientRelations A B C D h with ⟨h₃, h₄, h₅, h₆⟩
  linarith

theorem gap11 (x : ℝ) :
    integrand x =
      4 * (x + 3) / (5 * q₁ x) -
        (4 * x + 3) / (5 * q₂ x) := by
  rcases quadraticDenominators_ne_zero x with ⟨hq₁, hq₂⟩
  unfold integrand
  field_simp [hq₁, hq₂] <;>
    simp only [q₁, q₂] <;>
    ring

theorem gap12 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  rcases quadraticDenominators_ne_zero x with ⟨hq₁, hq₂⟩
  have hratio : q₁ x / q₂ x ≠ 0 := div_ne_zero hq₁ hq₂
  have hq₁d : HasDerivAt q₁ (2 * x + 2) x := by
    convert
      ((((hasDerivAt_id x).pow 2).add
        ((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x))).add
          (hasDerivAt_const x (2 : ℝ))) using 1 <;>
      simp [q₁] <;> ring
  have hq₂d : HasDerivAt q₂ (2 * x + 1) x := by
    convert
      ((((hasDerivAt_id x).pow 2).add (hasDerivAt_id x)).add
        (hasDerivAt_const x (1 / 2 : ℝ))) using 1 <;>
      simp [q₂] <;> ring
  have hxp1 : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
    simpa using ((hasDerivAt_id x).add_const (1 : ℝ))
  have h2xp1 : HasDerivAt (fun y : ℝ => 2 * y + 1) 2 x := by
    simpa using
      (((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)).add_const (1 : ℝ))
  have hlog :=
    (Real.hasDerivAt_log hratio).comp x (hq₁d.div hq₂d hq₂)
  have hlog₀ :
      HasDerivAt (fun y : ℝ => Real.log (q₁ y / q₂ y))
        ((q₁ x / q₂ x)⁻¹ *
          (((2 * x + 2) * q₂ x - q₁ x * (2 * x + 1)) / (q₂ x) ^ 2)) x := by
    simpa [Function.comp_def] using hlog
  have hlog' :
      HasDerivAt (fun y : ℝ => Real.log (q₁ y / q₂ y))
        ((2 * x + 2) / q₁ x - (2 * x + 1) / q₂ x) x := by
    convert hlog₀ using 1
    field_simp [hq₁, hq₂, hratio]
  have hatan₁ := (Real.hasDerivAt_arctan (x + 1)).comp x hxp1
  have hatan₂ := (Real.hasDerivAt_arctan (2 * x + 1)).comp x h2xp1
  have hden₁ : 1 + (x + 1) ^ 2 = q₁ x := by
    unfold q₁
    ring
  have hden₂ : 1 + (2 * x + 1) ^ 2 = 4 * q₂ x := by
    unfold q₂
    ring
  have hatan₁' :
      HasDerivAt (fun y : ℝ => Real.arctan (y + 1)) (1 / q₁ x) x := by
    have ht :
        HasDerivAt (fun y : ℝ => Real.arctan (y + 1))
          (1 / (1 + (x + 1) ^ 2) * 1) x := by
      simpa [Function.comp_def] using hatan₁
    rw [hden₁] at ht
    simpa using ht
  have hatan₂' :
      HasDerivAt (fun y : ℝ => Real.arctan (2 * y + 1))
        (1 / (2 * q₂ x)) x := by
    have ht :
        HasDerivAt (fun y : ℝ => Real.arctan (2 * y + 1))
          (1 / (1 + (2 * x + 1) ^ 2) * 2) x := by
      simpa [Function.comp_def] using hatan₂
    rw [hden₂] at ht
    convert ht using 1
    field_simp [hq₂]
    ring
  have hp :
      HasDerivAt primitive
        ((2 / 5 : ℝ) *
            ((2 * x + 2) / q₁ x - (2 * x + 1) / q₂ x) +
          (8 / 5 : ℝ) * (1 / q₁ x) -
          (2 / 5 : ℝ) * (1 / (2 * q₂ x))) x := by
    simpa only [primitive] using
      ((hlog'.const_mul (2 / 5 : ℝ)).add
        (hatan₁'.const_mul (8 / 5 : ℝ))).sub
          (hatan₂'.const_mul (2 / 5 : ℝ))
  rw [gap11 x]
  convert hp using 1
  field_simp [hq₁, hq₂]
  ring

theorem gap13 :
    Family integrand = Translates primitive := by
  ext F
  change IsAntiderivative F integrand ↔ ∃ C, ∀ x, F x = primitive x + C
  constructor
  · intro hF
    refine ⟨F 0 - primitive 0, ?_⟩
    have hz : ∀ y, HasDerivAt (fun t => F t - primitive t) 0 y := by
      intro y
      simpa using (hF y).sub (gap12 y)
    have hdiff : Differentiable ℝ (fun t => F t - primitive t) :=
      fun y => (hz y).differentiableAt
    have hderiv : ∀ y, deriv (fun t => F t - primitive t) y = 0 :=
      fun y => (hz y).deriv
    intro x
    have hc : F x - primitive x = F 0 - primitive 0 := by
      exact (is_const_of_deriv_eq_zero hdiff hderiv) x 0
    linarith
  · rintro ⟨C, hC⟩
    have hfun : F = fun x => primitive x + C := funext hC
    rw [hfun]
    intro x
    exact (gap12 x).add_const C

end

end ProofGap.Exercise1889
