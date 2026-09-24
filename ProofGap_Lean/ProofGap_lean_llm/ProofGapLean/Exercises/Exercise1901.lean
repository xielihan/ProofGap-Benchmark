import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1901

noncomputable section

def q (x : ℝ) : ℝ := x ^ 2 + x + 1
def denominator (x : ℝ) : ℝ := x ^ 4 + 2 * x ^ 3 + 3 * x ^ 2 + 2 * x + 1
def integrand (x : ℝ) : ℝ := 1 / denominator x
def primitive (x : ℝ) : ℝ :=
  (2 * x + 1) / (3 * q x) +
    4 / (3 * Real.sqrt 3) *
      Real.arctan ((2 * x + 1) / Real.sqrt 3)
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}
def CoeffIdentity (A B C D : ℝ) : Prop :=
  ∀ x, 1 =
    A * q x - (2 * x + 1) * (A * x + B) +
      (C * x + D) * q x

theorem gap1 (x : ℝ) :
    denominator x = q x ^ 2 := by
  unfold denominator q
  ring

theorem gap2 :
    ∃ A B C D : ℝ, CoeffIdentity A B C D := by
  refine ⟨(2 / 3 : ℝ), (1 / 3 : ℝ), 0, (2 / 3 : ℝ), ?_⟩
  intro x
  dsimp [CoeffIdentity, q]
  ring

theorem gap3 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    A = 2 / 3 := by
  have h0 := h (0 : ℝ)
  have h1 := h (1 : ℝ)
  have hm1 := h (-1 : ℝ)
  have h2 := h (2 : ℝ)
  norm_num [q] at h0 h1 hm1 h2
  linarith

theorem gap4 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    B = 1 / 3 := by
  have hA : A = 2 / 3 := gap3 A B C D h
  have h0 := h (0 : ℝ)
  have h1 := h (1 : ℝ)
  have hm1 := h (-1 : ℝ)
  norm_num [q] at h0 h1 hm1
  linarith

theorem gap5 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    C = 0 := by
  have hA : A = 2 / 3 := gap3 A B C D h
  have hB : B = 1 / 3 := gap4 A B C D h
  have h0 := h (0 : ℝ)
  have hm1 := h (-1 : ℝ)
  norm_num [q] at h0 hm1
  linarith

theorem gap6 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    D = 2 / 3 := by
  have hA : A = 2 / 3 := gap3 A B C D h
  have hB : B = 1 / 3 := gap4 A B C D h
  have h0 := h (0 : ℝ)
  norm_num [q] at h0
  linarith

theorem gap7 (x : ℝ) :
    HasDerivAt
      (fun y => (2 * y + 1) / (3 * q y) +
        (2 / 3 : ℝ) * Real.arctan ((2 * y + 1) / Real.sqrt 3) *
          (2 / Real.sqrt 3))
      (integrand x) x := by
  have hq_pos : 0 < q x := by
    unfold q
    nlinarith [sq_nonneg (x + (1 / 2 : ℝ))]
  have hq : q x ≠ 0 := ne_of_gt hq_pos
  have hsqrt_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_ne : Real.sqrt 3 ≠ 0 := ne_of_gt hsqrt_pos
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hn : HasDerivAt (fun y : ℝ => 2 * y + 1) 2 x := by
    simpa using ((hasDerivAt_id x).const_mul 2).add_const 1
  have hq' : HasDerivAt q (2 * x + 1) x := by
    simpa [q] using
      ((((hasDerivAt_id x).pow 2).add (hasDerivAt_id x)).add
        (hasDerivAt_const x (1 : ℝ)))
  have hfirst :
      HasDerivAt
        (fun y : ℝ => (2 * y + 1) / (3 * q y))
        ((2 * (3 * q x) - (2 * x + 1) * (3 * (2 * x + 1))) /
          (3 * q x) ^ 2) x := by
    exact hn.div (hq'.const_mul 3) (mul_ne_zero (by norm_num) hq)
  have hz :
      HasDerivAt
        (fun y : ℝ => (2 * y + 1) / Real.sqrt 3)
        (2 / Real.sqrt 3) x := by
    exact hn.div_const (Real.sqrt 3)
  have hatan :
      HasDerivAt
        (fun y : ℝ => Real.arctan ((2 * y + 1) / Real.sqrt 3))
        ((1 / (1 + ((2 * x + 1) / Real.sqrt 3) ^ 2)) *
          (2 / Real.sqrt 3)) x := by
    simpa using
      (Real.hasDerivAt_arctan ((2 * x + 1) / Real.sqrt 3)).comp x hz
  have hsecond :
      HasDerivAt
        (fun y : ℝ =>
          (2 / 3 : ℝ) * Real.arctan ((2 * y + 1) / Real.sqrt 3) *
            (2 / Real.sqrt 3))
        (((2 / 3 : ℝ) *
            ((1 / (1 + ((2 * x + 1) / Real.sqrt 3) ^ 2)) *
              (2 / Real.sqrt 3))) *
          (2 / Real.sqrt 3)) x := by
    exact (hatan.const_mul (2 / 3 : ℝ)).mul_const (2 / Real.sqrt 3)
  have hangle_eq :
      1 + ((2 * x + 1) / Real.sqrt 3) ^ 2 = 4 * q x / 3 := by
    calc
      1 + ((2 * x + 1) / Real.sqrt 3) ^ 2 =
          ((Real.sqrt 3) ^ 2 + (2 * x + 1) ^ 2) /
            (Real.sqrt 3) ^ 2 := by
              field_simp [hsqrt_ne]
              <;> ring
      _ = (3 + (2 * x + 1) ^ 2) / 3 := by rw [hsqrt_sq]
      _ = 4 * q x / 3 := by
        unfold q
        ring
  have hsecond_eq :
      ((2 / 3 : ℝ) *
          ((1 / (1 + ((2 * x + 1) / Real.sqrt 3) ^ 2)) *
            (2 / Real.sqrt 3))) *
        (2 / Real.sqrt 3) = 2 / (3 * q x) := by
    calc
      _ = 2 / (q x * (Real.sqrt 3) ^ 2) := by
        rw [hangle_eq]
        field_simp [hq, hsqrt_ne]
        <;> ring
      _ = 2 / (3 * q x) := by
        rw [hsqrt_sq]
        ring
  have hvalue :
      (2 * (3 * q x) - (2 * x + 1) * (3 * (2 * x + 1))) /
            (3 * q x) ^ 2 +
          (((2 / 3 : ℝ) *
              ((1 / (1 + ((2 * x + 1) / Real.sqrt 3) ^ 2)) *
                (2 / Real.sqrt 3))) *
            (2 / Real.sqrt 3)) = integrand x := by
    rw [hsecond_eq]
    rw [integrand, gap1]
    field_simp [hq]
    unfold q
    ring
  rw [← hvalue]
  exact hfirst.add hsecond

theorem gap8 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hsqrt_ne : Real.sqrt 3 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hfun :
      primitive =
        (fun y => (2 * y + 1) / (3 * q y) +
          (2 / 3 : ℝ) * Real.arctan ((2 * y + 1) / Real.sqrt 3) *
            (2 / Real.sqrt 3)) := by
    funext y
    unfold primitive
    field_simp [hsqrt_ne]
    <;> ring
  rw [hfun]
  exact gap7 x

theorem gap9 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  exact gap8 x

theorem gap10 :
    Family integrand = Translates primitive := by
  apply Set.ext
  intro F
  change IsAntiderivative F integrand ↔
    ∃ C, ∀ x, F x = primitive x + C
  constructor
  · intro hF
    let G : ℝ → ℝ := fun y => F y - primitive y
    have hG (y : ℝ) : HasDerivAt G 0 y := by
      simpa [G] using (hF y).sub (gap9 y)
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hconst : G x = G 0 := by
      rcases lt_trichotomy x 0 with hx | hx | hx
      · obtain ⟨c, hc, hder⟩ :=
          exists_deriv_eq_slope (f := G) hx
            (fun y hy => (hG y).continuousAt.continuousWithinAt)
            (fun y hy => (hG y).differentiableAt.differentiableWithinAt)
        have hcder : deriv G c = 0 := (hG c).deriv
        rw [hcder] at hder
        have hden : (0 : ℝ) - x ≠ 0 := by linarith
        field_simp [hden] at hder
        linarith
      · simpa [hx]
      · obtain ⟨c, hc, hder⟩ :=
          exists_deriv_eq_slope (f := G) hx
            (fun y hy => (hG y).continuousAt.continuousWithinAt)
            (fun y hy => (hG y).differentiableAt.differentiableWithinAt)
        have hcder : deriv G c = 0 := (hG c).deriv
        rw [hcder] at hder
        have hden : x - (0 : ℝ) ≠ 0 := by linarith
        field_simp [hden] at hder
        linarith
    dsimp [G] at hconst
    linarith
  · rintro ⟨C, hC⟩
    intro x
    have hEq : F = fun y => primitive y + C := funext hC
    rw [hEq]
    simpa using (gap9 x).add_const C

end

end ProofGap.Exercise1901
