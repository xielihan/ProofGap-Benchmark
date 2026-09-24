import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1896

noncomputable section

def q (x : ℝ) : ℝ := x ^ 2 + x + 1
def integrand (x : ℝ) : ℝ :=
  (x ^ 2 + 3 * x - 2) / ((x - 1) * q x ^ 2)
def domain : Set ℝ := {x | x ≠ 1}
def primitive (x : ℝ) : ℝ :=
  (5 * x + 2) / (3 * q x) +
    (1 / 9 : ℝ) * Real.log ((x - 1) ^ 2 / q x) +
    8 / (3 * Real.sqrt 3) *
      Real.arctan ((2 * x + 1) / Real.sqrt 3)
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}
def CoeffIdentity (A B C D E : ℝ) : Prop :=
  ∀ x, x ^ 2 + 3 * x - 2 =
    A * (x - 1) * q x -
      (2 * x + 1) * (A * x + B) * (x - 1) +
      (C * x ^ 2 + D * x + E) * q x

private theorem coefficients_unique (A B C D E : ℝ)
    (h : CoeffIdentity A B C D E) :
    A = 5 / 3 ∧ B = 2 / 3 ∧ C = 0 ∧ D = 5 / 3 ∧ E = -1 := by
  have h0 := h (0 : ℝ)
  have h1 := h (1 : ℝ)
  have hm1 := h (-1 : ℝ)
  have h2 := h (2 : ℝ)
  have hm2 := h (-2 : ℝ)
  norm_num [q] at h0 h1 hm1 h2 hm2
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private theorem q_pos (x : ℝ) : 0 < q x := by
  unfold q
  nlinarith [sq_nonneg (x + 1 / 2)]

private theorem hasDerivAt_q (x : ℝ) : HasDerivAt q (2 * x + 1) x := by
  unfold q
  convert (((hasDerivAt_id x).pow 2).add (hasDerivAt_id x)).add
      (hasDerivAt_const x (1 : ℝ)) using 1 <;> simp <;> ring

theorem gap1 :
    ∃ A B C D E : ℝ, CoeffIdentity A B C D E := by
  refine ⟨5 / 3, 2 / 3, 0, 5 / 3, -1, ?_⟩
  intro x
  unfold q
  ring

theorem gap2 (A B C D E x : ℝ) (h : CoeffIdentity A B C D E) :
    x ^ 2 + 3 * x - 2 =
      A * (x - 1) * q x -
        (2 * x + 1) * (A * x + B) * (x - 1) +
        (C * x ^ 2 + D * x + E) * q x := by
  exact h x

theorem gap3 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    C = 0 := by
  exact (coefficients_unique A B C D E h).2.2.1

theorem gap4 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    -A + C + D = 0 := by
  rcases coefficients_unique A B C D E h with ⟨hA, hB, hC, hD, hE⟩
  norm_num [hA, hC, hD]

theorem gap5 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    A - 2 * B + C + D + E = 1 := by
  rcases coefficients_unique A B C D E h with ⟨hA, hB, hC, hD, hE⟩
  norm_num [hA, hB, hC, hD, hE]

theorem gap6 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    A + B + D + E = 3 := by
  rcases coefficients_unique A B C D E h with ⟨hA, hB, hC, hD, hE⟩
  norm_num [hA, hB, hD, hE]

theorem gap7 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    -A + B + E = -2 := by
  rcases coefficients_unique A B C D E h with ⟨hA, hB, hC, hD, hE⟩
  norm_num [hA, hB, hE]

theorem gap8 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    A = 5 / 3 := by
  exact (coefficients_unique A B C D E h).1

theorem gap9 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    B = 2 / 3 := by
  exact (coefficients_unique A B C D E h).2.1

theorem gap10 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    C = 0 := by
  exact (coefficients_unique A B C D E h).2.2.1

theorem gap11 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    D = 5 / 3 := by
  exact (coefficients_unique A B C D E h).2.2.2.1

theorem gap12 (A B C D E : ℝ) (h : CoeffIdentity A B C D E) :
    E = -1 := by
  exact (coefficients_unique A B C D E h).2.2.2.2

theorem gap13 (x : ℝ) (hx : x ∈ domain) :
    ((5 / 3 : ℝ) * x - 1) / ((x - 1) * q x) =
      2 / (9 * (x - 1)) - (2 * x - 11) / (9 * q x) := by
  have hxne : x ≠ 1 := by
    simpa [domain] using hx
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hxne
  have hq0 : q x ≠ 0 := ne_of_gt (q_pos x)
  field_simp [hx1, hq0]
  unfold q
  ring

theorem gap14 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  change HasDerivAt
    (fun y =>
      (5 * y + 2) / (3 * q y) +
        (1 / 9 : ℝ) * Real.log ((y - 1) ^ 2 / q y) +
        8 / (3 * Real.sqrt 3) *
          Real.arctan ((2 * y + 1) / Real.sqrt 3))
    ((x ^ 2 + 3 * x - 2) / ((x - 1) * q x ^ 2)) x
  have hxne : x ≠ 1 := by
    simpa [domain] using hx
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hxne
  have hq0 : q x ≠ 0 := ne_of_gt (q_pos x)
  have hsqrt : Real.sqrt 3 ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hq : HasDerivAt q (2 * x + 1) x := hasDerivAt_q x
  have hnum : HasDerivAt (fun y : ℝ => 5 * y + 2) 5 x := by
    simpa using ((hasDerivAt_id x).const_mul 5).add_const 2
  have hden : HasDerivAt (fun y : ℝ => 3 * q y) (3 * (2 * x + 1)) x := by
    simpa using hq.const_mul 3
  have hfrac :
      HasDerivAt (fun y : ℝ => (5 * y + 2) / (3 * q y))
        ((5 * (3 * q x) - (5 * x + 2) * (3 * (2 * x + 1))) /
          (3 * q x) ^ 2) x := by
    exact hnum.div hden (mul_ne_zero (by norm_num) hq0)
  have hsub : HasDerivAt (fun y : ℝ => y - 1) 1 x := by
    simpa using (hasDerivAt_id x).sub_const 1
  have hsq : HasDerivAt (fun y : ℝ => (y - 1) ^ 2) (2 * (x - 1)) x := by
    convert hsub.pow 2 using 1 <;> ring
  have hratio :
      HasDerivAt (fun y : ℝ => (y - 1) ^ 2 / q y)
        (((2 * (x - 1)) * q x - (x - 1) ^ 2 * (2 * x + 1)) /
          (q x) ^ 2) x := by
    exact hsq.div hq hq0
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log ((y - 1) ^ 2 / q y))
        ((((2 * (x - 1)) * q x - (x - 1) ^ 2 * (2 * x + 1)) /
            (q x) ^ 2) / ((x - 1) ^ 2 / q x)) x := by
    exact hratio.log (div_ne_zero (pow_ne_zero 2 hx1) hq0)
  have hlin : HasDerivAt (fun y : ℝ => 2 * y + 1) 2 x := by
    simpa using ((hasDerivAt_id x).const_mul 2).add_const 1
  have harg :
      HasDerivAt (fun y : ℝ => (2 * y + 1) / Real.sqrt 3)
        (2 / Real.sqrt 3) x := by
    simpa using hlin.div_const (Real.sqrt 3)
  have hatan :
      HasDerivAt
        (fun y : ℝ => Real.arctan ((2 * y + 1) / Real.sqrt 3))
        ((2 / Real.sqrt 3) /
          (1 + ((2 * x + 1) / Real.sqrt 3) ^ 2)) x := by
    convert harg.arctan using 1 <;> ring
  have htotal :
      HasDerivAt
        (fun y =>
          (5 * y + 2) / (3 * q y) +
            (1 / 9 : ℝ) * Real.log ((y - 1) ^ 2 / q y) +
            8 / (3 * Real.sqrt 3) *
              Real.arctan ((2 * y + 1) / Real.sqrt 3))
        (((5 * (3 * q x) - (5 * x + 2) * (3 * (2 * x + 1))) /
            (3 * q x) ^ 2) +
          (1 / 9 : ℝ) *
            ((((2 * (x - 1)) * q x - (x - 1) ^ 2 * (2 * x + 1)) /
                (q x) ^ 2) / ((x - 1) ^ 2 / q x)) +
          8 / (3 * Real.sqrt 3) *
            ((2 / Real.sqrt 3) /
              (1 + ((2 * x + 1) / Real.sqrt 3) ^ 2))) x := by
    simpa using
      (hfrac.add (hlog.const_mul (1 / 9 : ℝ))).add
        (hatan.const_mul (8 / (3 * Real.sqrt 3)))
  convert htotal using 1
  field_simp [hx1, hq0, hsqrt]
  unfold q
  ring_nf
  simp only [hsqrt_sq] <;> ring

theorem gap15 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt
      (fun y =>
        (5 * y + 2) / (3 * q y) +
          (2 / 9 : ℝ) * Real.log |y - 1| -
          (1 / 9 : ℝ) * Real.log (q y) +
          8 / (3 * Real.sqrt 3) *
            Real.arctan ((2 * y + 1) / Real.sqrt 3))
      (integrand x) x := by
  change HasDerivAt
    (fun y =>
      (5 * y + 2) / (3 * q y) +
        (2 / 9 : ℝ) * Real.log |y - 1| -
        (1 / 9 : ℝ) * Real.log (q y) +
        8 / (3 * Real.sqrt 3) *
          Real.arctan ((2 * y + 1) / Real.sqrt 3))
    ((x ^ 2 + 3 * x - 2) / ((x - 1) * q x ^ 2)) x
  have hxne : x ≠ 1 := by
    simpa [domain] using hx
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hxne
  have hq0 : q x ≠ 0 := ne_of_gt (q_pos x)
  have hsqrt : Real.sqrt 3 ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hq : HasDerivAt q (2 * x + 1) x := hasDerivAt_q x
  have hnum : HasDerivAt (fun y : ℝ => 5 * y + 2) 5 x := by
    simpa using ((hasDerivAt_id x).const_mul 5).add_const 2
  have hden : HasDerivAt (fun y : ℝ => 3 * q y) (3 * (2 * x + 1)) x := by
    simpa using hq.const_mul 3
  have hfrac :
      HasDerivAt (fun y : ℝ => (5 * y + 2) / (3 * q y))
        ((5 * (3 * q x) - (5 * x + 2) * (3 * (2 * x + 1))) /
          (3 * q x) ^ 2) x := by
    exact hnum.div hden (mul_ne_zero (by norm_num) hq0)
  have hsub : HasDerivAt (fun y : ℝ => y - 1) 1 x := by
    simpa using (hasDerivAt_id x).sub_const 1
  have hlogabs :
      HasDerivAt (fun y : ℝ => Real.log |y - 1|) (1 / (x - 1)) x := by
    simpa only [Real.log_abs] using hsub.log hx1
  have hlogq :
      HasDerivAt (fun y : ℝ => Real.log (q y)) ((2 * x + 1) / q x) x := by
    exact hq.log hq0
  have hlin : HasDerivAt (fun y : ℝ => 2 * y + 1) 2 x := by
    simpa using ((hasDerivAt_id x).const_mul 2).add_const 1
  have harg :
      HasDerivAt (fun y : ℝ => (2 * y + 1) / Real.sqrt 3)
        (2 / Real.sqrt 3) x := by
    simpa using hlin.div_const (Real.sqrt 3)
  have hatan :
      HasDerivAt
        (fun y : ℝ => Real.arctan ((2 * y + 1) / Real.sqrt 3))
        ((2 / Real.sqrt 3) /
          (1 + ((2 * x + 1) / Real.sqrt 3) ^ 2)) x := by
    convert harg.arctan using 1 <;> ring
  have htotal :
      HasDerivAt
        (fun y =>
          (5 * y + 2) / (3 * q y) +
            (2 / 9 : ℝ) * Real.log |y - 1| -
            (1 / 9 : ℝ) * Real.log (q y) +
            8 / (3 * Real.sqrt 3) *
              Real.arctan ((2 * y + 1) / Real.sqrt 3))
        ((((5 * (3 * q x) - (5 * x + 2) * (3 * (2 * x + 1))) /
              (3 * q x) ^ 2) +
            (2 / 9 : ℝ) * (1 / (x - 1)) -
            (1 / 9 : ℝ) * ((2 * x + 1) / q x)) +
          8 / (3 * Real.sqrt 3) *
            ((2 / Real.sqrt 3) /
              (1 + ((2 * x + 1) / Real.sqrt 3) ^ 2))) x := by
    simpa using
      (((hfrac.add (hlogabs.const_mul (2 / 9 : ℝ))).sub
          (hlogq.const_mul (1 / 9 : ℝ))).add
        (hatan.const_mul (8 / (3 * Real.sqrt 3))))
  convert htotal using 1
  field_simp [hx1, hq0, hsqrt]
  unfold q
  ring_nf
  simp only [hsqrt_sq] <;> ring

theorem gap16 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand s at hF
    change ∃ C : ℝ, ∀ x ∈ s, F x = primitive x + C
    by_cases hne : s.Nonempty
    · rcases hne with ⟨x₀, hx₀⟩
      have hzero :
          ∀ x ∈ s, HasDerivAt (fun y => F y - primitive y) 0 x := by
        intro x hx
        convert (hF x hx).sub (gap14 x (hdom hx)) using 1 <;> ring
      have hdiff :
          DifferentiableOn ℝ (fun y => F y - primitive y) s := by
        intro x hx
        exact (hzero x hx).differentiableAt.differentiableWithinAt
      have hderiv :
          ∀ x ∈ s, deriv (fun y => F y - primitive y) x = 0 := by
        intro x hx
        exact (hzero x hx).deriv
      refine ⟨F x₀ - primitive x₀, ?_⟩
      intro x hx
      have heq :
          (fun y => F y - primitive y) x₀ =
            (fun y => F y - primitive y) x :=
        hopen.is_const_of_deriv_eq_zero hs hdiff hderiv hx₀ hx
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hne ⟨x, hx⟩).elim
  · intro hF
    change ∃ C : ℝ, ∀ x ∈ s, F x = primitive x + C at hF
    change IsAntiderivativeOn F integrand s
    rcases hF with ⟨C, hC⟩
    intro x hx
    have hbase :
        HasDerivAt (fun y => primitive y + C) (integrand x) x :=
      (gap14 x (hdom hx)).add_const C
    apply hbase.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hC y hy

end

end ProofGap.Exercise1896
