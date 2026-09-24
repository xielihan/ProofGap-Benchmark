import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1894

noncomputable section

def q (x : ℝ) : ℝ := x ^ 2 + 2 * x + 2
def integrand (x : ℝ) : ℝ := x ^ 2 / q x ^ 2
def primitive (x : ℝ) : ℝ := 1 / q x + Real.arctan (x + 1)
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}
def CoeffIdentity (A B C D : ℝ) : Prop :=
  ∀ x, x ^ 2 =
    A * q x - 2 * (x + 1) * (A * x + B) +
      (C * x + D) * q x

theorem gap1 (x : ℝ) :
    integrand x = (q x - (2 * x + 2)) / q x ^ 2 := by
  unfold integrand q
  ring

theorem gap2 :
    ∃ A B C D : ℝ, CoeffIdentity A B C D := by
  refine ⟨0, 1, 0, 1, ?_⟩
  intro x
  unfold q
  ring

theorem gap3 (A B C D x : ℝ) (h : CoeffIdentity A B C D) :
    x ^ 2 =
      A * q x - 2 * (x + 1) * (A * x + B) +
        (C * x + D) * q x := by
  exact h x

theorem gap4 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    C = 0 := by
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  norm_num [q] at h0 h1 hm1 h2
  linarith

theorem gap5 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    -A + 2 * C + D = 1 := by
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  norm_num [q] at h0 h1 hm1 h2
  linarith

theorem gap6 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    -2 * B + 2 * C + 2 * D = 0 := by
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  norm_num [q] at h0 h1 hm1 h2
  linarith

theorem gap7 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    2 * A - 2 * B + 2 * D = 0 := by
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  norm_num [q] at h0 h1 hm1 h2
  linarith

theorem gap8 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    A = 0 := by
  have h4 := gap4 A B C D h
  have h5 := gap5 A B C D h
  have h6 := gap6 A B C D h
  have h7 := gap7 A B C D h
  linarith

theorem gap9 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    B = 1 := by
  have h4 := gap4 A B C D h
  have h5 := gap5 A B C D h
  have h6 := gap6 A B C D h
  have h8 := gap8 A B C D h
  linarith

theorem gap10 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    C = 0 := by
  exact gap4 A B C D h

theorem gap11 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    D = 1 := by
  have h4 := gap4 A B C D h
  have h5 := gap5 A B C D h
  have h8 := gap8 A B C D h
  linarith

theorem gap12 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hq_pos : 0 < q x := by
    unfold q
    nlinarith [sq_nonneg (x + 1)]
  have hq_ne : q x ≠ 0 := ne_of_gt hq_pos
  have hq_deriv : HasDerivAt q (2 * x + 2) x := by
    unfold q
    convert
      (((hasDerivAt_id x).pow 2).add
        (((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)).add_const 2)) using 1
    · ext y
      simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
      ring
    · simp only [id_eq]
      ring
  have hinv : HasDerivAt (fun y : ℝ => 1 / q y)
      (-(2 * x + 2) / q x ^ 2) x := by
    convert (hasDerivAt_const x (1 : ℝ)).div hq_deriv hq_ne using 1 <;> ring
  have hatan : HasDerivAt (fun y : ℝ => Real.arctan (y + 1))
      (1 / q x) x := by
    convert
      (Real.hasDerivAt_arctan (x + 1)).comp x
        ((hasDerivAt_id x).add_const 1) using 1
    unfold q
    ring
  have hsum : HasDerivAt primitive
      (-(2 * x + 2) / q x ^ 2 + 1 / q x) x := by
    simpa only [primitive] using hinv.add hatan
  convert hsum using 1
  rw [gap1 x]
  field_simp [hq_ne] <;> ring

theorem gap13 (x : ℝ) :
    primitive x = 1 / ((x + 1) ^ 2 + 1) + Real.arctan (x + 1) := by
  unfold primitive q
  ring

theorem gap14 :
    Family integrand = Translates primitive := by
  ext F
  constructor
  · intro hF
    change IsAntiderivative F integrand at hF
    change ∃ C, ∀ x, F x = primitive x + C
    have hzero : ∀ x, HasDerivAt (fun y : ℝ => F y - primitive y) 0 x := by
      intro x
      convert (hF x).sub (gap12 x) using 1 <;> ring
    have hdiff : Differentiable ℝ (fun y : ℝ => F y - primitive y) :=
      fun x => (hzero x).differentiableAt
    have hmono : Monotone (fun y : ℝ => F y - primitive y) := by
      apply monotone_of_deriv_nonneg hdiff
      intro x
      rw [(hzero x).deriv]
    have hzero_neg : ∀ x, HasDerivAt
        (fun y : ℝ => -(F y - primitive y)) 0 x := by
      intro x
      convert (hzero x).neg using 1 <;> ring
    have hdiff_neg : Differentiable ℝ
        (fun y : ℝ => -(F y - primitive y)) :=
      fun x => (hzero_neg x).differentiableAt
    have hmono_neg : Monotone
        (fun y : ℝ => -(F y - primitive y)) := by
      apply monotone_of_deriv_nonneg hdiff_neg
      intro x
      rw [(hzero_neg x).deriv]
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have heq : F x - primitive x = F 0 - primitive 0 := by
      rcases le_total x 0 with hx | hx
      · have h1 : F x - primitive x ≤ F 0 - primitive 0 := hmono hx
        have h2 : -(F x - primitive x) ≤ -(F 0 - primitive 0) :=
          hmono_neg hx
        linarith
      · have h1 : F 0 - primitive 0 ≤ F x - primitive x := hmono hx
        have h2 : -(F 0 - primitive 0) ≤ -(F x - primitive x) :=
          hmono_neg hx
        linarith
    linarith
  · intro hF
    change (∃ C, ∀ x, F x = primitive x + C) at hF
    change IsAntiderivative F integrand
    rcases hF with ⟨C, hC⟩
    have hfun : F = fun y => primitive y + C := funext hC
    rw [hfun]
    intro x
    exact (gap12 x).add_const C

theorem gap15 (x : ℝ) :
    integrand x = 1 / q x - (2 * x + 2) / q x ^ 2 := by
  have hq_pos : 0 < q x := by
    unfold q
    nlinarith [sq_nonneg (x + 1)]
  have hq_ne : q x ≠ 0 := ne_of_gt hq_pos
  rw [gap1 x]
  field_simp [hq_ne] <;> ring

theorem gap16 (x : ℝ) :
    HasDerivAt primitive
      (1 / q x - (2 * x + 2) / q x ^ 2) x := by
  rw [← gap15 x]
  exact gap12 x

theorem gap17 :
    Family integrand = Translates primitive := by
  exact gap14

end

end ProofGap.Exercise1894
