import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1880

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / (x * (1 + x) * (1 + x + x ^ 2))
def domain : Set ℝ := {x | x ≠ 0 ∧ x ≠ -1}
def primitive (x : ℝ) : ℝ :=
  Real.log |x / (1 + x)| -
    2 / Real.sqrt 3 * Real.arctan ((2 * x + 1) / Real.sqrt 3)
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}
def CoeffIdentity (A B C D : ℝ) : Prop :=
  ∀ x, 1 =
    A * (x + 1) * (1 + x + x ^ 2) +
      B * x * (1 + x + x ^ 2) +
      x * (x + 1) * (C * x + D)

private theorem coeffIdentity_values (A B C D : ℝ)
    (h : CoeffIdentity A B C D) :
    A = 1 ∧ B = -1 ∧ C = 0 ∧ D = -1 := by
  have h0 := h 0
  have hm1 := h (-1)
  have h1 := h 1
  have h2 := h 2
  norm_num at h0 hm1 h1 h2
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

private theorem integrand_decomposition (x : ℝ) (hx : x ∈ domain) :
    integrand x =
      1 / x - 1 / (1 + x) - 1 / (1 + x + x ^ 2) := by
  rcases hx with ⟨hx0, hxneg⟩
  have hx1 : 1 + x ≠ 0 := by
    intro hzero
    apply hxneg
    linarith
  have hxp1 : x + 1 ≠ 0 := by
    intro hzero
    apply hxneg
    linarith
  have hq : 1 + x + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (2 * x + 1)]
  unfold integrand
  field_simp [hx0, hx1, hxp1, hq]
  <;> ring

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  rcases hx with ⟨hx0, hxneg⟩
  have hx1 : 1 + x ≠ 0 := by
    intro hzero
    apply hxneg
    linarith
  have hu : x / (1 + x) ≠ 0 := div_ne_zero hx0 hx1
  have hsqrt : Real.sqrt 3 ≠ 0 := by positivity
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have hq : 1 + x + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (2 * x + 1)]
  have hdenlin : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
  have hquot := (hasDerivAt_id x).div hdenlin hx1
  have hlog0 := hquot.log hu
  have hlog :
      HasDerivAt (fun y => Real.log (y / (1 + y)))
        (1 / x - 1 / (1 + x)) x := by
    convert hlog0 using 1
    dsimp
    field_simp [hx0, hx1]
    <;> ring
  have hlinear : HasDerivAt (fun y : ℝ => 2 * y + 1) 2 x := by
    convert ((hasDerivAt_id x).const_mul (2 : ℝ)).add_const 1 using 1 <;> ring
  have hratio0 := hlinear.div (hasDerivAt_const x (Real.sqrt 3)) hsqrt
  have hratio :
      HasDerivAt (fun y => (2 * y + 1) / Real.sqrt 3)
        (2 / Real.sqrt 3) x := by
    convert hratio0 using 1
    dsimp
    field_simp [hsqrt]
    <;> ring
  have hatan :=
    (Real.hasDerivAt_arctan ((2 * x + 1) / Real.sqrt 3)).comp x hratio
  have hden :
      (Real.sqrt 3) ^ 2 + (2 * x + 1) ^ 2 =
        4 * (1 + x + x ^ 2) := by
    rw [hsqrt_sq]
    ring
  have hsum :
      (Real.sqrt 3) ^ 2 + (2 * x + 1) ^ 2 ≠ 0 := by
    rw [hden]
    exact mul_ne_zero (by norm_num) hq
  have hatden : 1 + ((2 * x + 1) / Real.sqrt 3) ^ 2 ≠ 0 := by
    positivity
  have hcoef :
      2 / Real.sqrt 3 *
          (1 / (1 + ((2 * x + 1) / Real.sqrt 3) ^ 2) *
            (2 / Real.sqrt 3)) =
        1 / (1 + x + x ^ 2) := by
    calc
      2 / Real.sqrt 3 *
          (1 / (1 + ((2 * x + 1) / Real.sqrt 3) ^ 2) *
            (2 / Real.sqrt 3)) =
          4 / ((Real.sqrt 3) ^ 2 + (2 * x + 1) ^ 2) := by
            field_simp [hsqrt, hatden, hsum]
            <;> ring
      _ = 1 / (1 + x + x ^ 2) := by
        rw [hden]
        field_simp [hq]
        <;> ring
  have hscaled :
      HasDerivAt
        (fun y => 2 / Real.sqrt 3 *
          Real.arctan ((2 * y + 1) / Real.sqrt 3))
        (1 / (1 + x + x ^ 2)) x := by
    simpa only [Function.comp_apply, hcoef] using
      hatan.const_mul (2 / Real.sqrt 3)
  have hprimitive :
      primitive = fun y =>
        Real.log (y / (1 + y)) -
          2 / Real.sqrt 3 * Real.arctan ((2 * y + 1) / Real.sqrt 3) := by
    funext y
    simp [primitive, Real.log_abs]
  rw [hprimitive]
  rw [integrand_decomposition x ⟨hx0, hxneg⟩]
  exact hlog.sub hscaled

theorem gap1 :
    ∃ A B C D : ℝ, CoeffIdentity A B C D := by
  refine ⟨1, -1, 0, -1, ?_⟩
  intro x
  ring

theorem gap2 (A B C D x : ℝ) (h : CoeffIdentity A B C D) :
    1 =
      A * (x + 1) * (1 + x + x ^ 2) +
        B * x * (1 + x + x ^ 2) +
        x * (x + 1) * (C * x + D) := by
  exact h x

theorem gap3 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    A + B + C = 0 := by
  rcases coeffIdentity_values A B C D h with ⟨hA, hB, hC, hD⟩
  rw [hA, hB, hC]
  norm_num

theorem gap4 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    2 * A + B + C + D = 0 := by
  rcases coeffIdentity_values A B C D h with ⟨hA, hB, hC, hD⟩
  rw [hA, hB, hC, hD]
  norm_num

theorem gap5 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    2 * A + B + D = 0 := by
  rcases coeffIdentity_values A B C D h with ⟨hA, hB, hC, hD⟩
  rw [hA, hB, hD]
  norm_num

theorem gap6 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    A = 1 := by
  exact (coeffIdentity_values A B C D h).1

theorem gap7 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    A = 1 := by
  exact gap6 A B C D h

theorem gap8 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    B = -1 := by
  exact (coeffIdentity_values A B C D h).2.1

theorem gap9 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    C = 0 := by
  exact (coeffIdentity_values A B C D h).2.2.1

theorem gap10 (A B C D : ℝ) (h : CoeffIdentity A B C D) :
    D = -1 := by
  exact (coeffIdentity_values A B C D h).2.2.2

theorem gap11 (x : ℝ) (hx : x ∈ domain) :
    integrand x =
      1 / x - 1 / (1 + x) - 1 / (1 + x + x ^ 2) := by
  exact integrand_decomposition x hx

theorem gap12 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand s at hF
    change F ∈ Translates primitive s
    have hzero : ∀ x ∈ s,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (primitive_hasDerivAt x (hdom hx))
    by_cases hne : s.Nonempty
    · rcases hne with ⟨x₀, hx₀⟩
      have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y) s := by
        intro x hx
        exact (hzero x hx).differentiableAt.differentiableWithinAt
      have hderiv : ∀ x ∈ s,
          deriv (fun y => F y - primitive y) x = 0 := by
        intro x hx
        exact (hzero x hx).deriv
      refine ⟨F x₀ - primitive x₀, ?_⟩
      intro x hx
      have heq : F x - primitive x = F x₀ - primitive x₀ :=
        hopen.is_const_of_deriv_eq_zero hs hdiff hderiv hx hx₀
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact False.elim (hne ⟨x, hx⟩)
  · intro hF
    change F ∈ Translates primitive s at hF
    change IsAntiderivativeOn F integrand s
    rcases hF with ⟨C, hC⟩
    intro x hx
    have hp := (primitive_hasDerivAt x (hdom hx)).add_const C
    have heq : Filter.EventuallyEq (nhds x) F (fun y => primitive y + C) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact hp.congr_of_eventuallyEq heq

theorem gap13 (x : ℝ) (hx : x ∈ domain) :
    1 / (x * (1 + x) * (1 + x + x ^ 2)) =
      1 / ((x + x ^ 2) * (1 + x + x ^ 2)) := by
  rw [show x * (1 + x) = x + x ^ 2 by ring]

theorem gap14 (x : ℝ) (hx : x ∈ domain) :
    1 / ((x + x ^ 2) * (1 + x + x ^ 2)) =
      1 / (x + x ^ 2) - 1 / (1 + x + x ^ 2) := by
  rcases hx with ⟨hx0, hxneg⟩
  have hx1 : 1 + x ≠ 0 := by
    intro hzero
    apply hxneg
    linarith
  have ha : x + x ^ 2 ≠ 0 := by
    rw [show x + x ^ 2 = x * (1 + x) by ring]
    exact mul_ne_zero hx0 hx1
  have hq : 1 + x + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (2 * x + 1)]
  field_simp [ha, hq]
  <;> ring

theorem gap15 (x : ℝ) (hx : x ∈ domain) :
    1 / (x + x ^ 2) - 1 / (1 + x + x ^ 2) =
      1 / x - 1 / (1 + x) - 1 / (1 + x + x ^ 2) := by
  rcases hx with ⟨hx0, hxneg⟩
  have hx1 : 1 + x ≠ 0 := by
    intro hzero
    apply hxneg
    linarith
  have ha : x + x ^ 2 ≠ 0 := by
    rw [show x + x ^ 2 = x * (1 + x) by ring]
    exact mul_ne_zero hx0 hx1
  field_simp [hx0, hx1, ha]
  <;> ring

theorem gap16 (x : ℝ) (hx : x ∈ domain) :
    1 / (x * (1 + x) * (1 + x + x ^ 2)) =
      1 / x - 1 / (1 + x) - 1 / (1 + x + x ^ 2) := by
  exact gap11 x hx

end

end ProofGap.Exercise1880
