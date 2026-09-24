import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1850

noncomputable section

def quadratic (a b c x : ℝ) : ℝ := a * x ^ 2 + b * x + c

def discriminant (a b c : ℝ) : ℝ := b ^ 2 - 4 * a * c

def integrand (a b c x : ℝ) : ℝ := 1 / Real.sqrt (quadratic a b c x)

def antiderivativesOn (s : Set ℝ) (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F s ∧ ∀ x ∈ s, deriv F x = g x}

def primitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}

def positiveCompletedIntegrand (a b c x : ℝ) : ℝ :=
  (1 / Real.sqrt a) /
    Real.sqrt ((x + b / (2 * a)) ^ 2 +
      (4 * a * c - b ^ 2) / (4 * a ^ 2))

def positivePrimitive (a b c x : ℝ) : ℝ :=
  (1 / Real.sqrt a) *
    Real.log |x + b / (2 * a) +
      Real.sqrt (x ^ 2 + (b / a) * x + c / a)|

def positiveDerivativePrimitive (a b c x : ℝ) : ℝ :=
  (1 / Real.sqrt a) *
    Real.log |(2 * a * x + b) / 2 +
      Real.sqrt (a * quadratic a b c x)|

def negativeRadius (a b c : ℝ) : ℝ :=
  Real.sqrt (discriminant a b c) / (-2 * a)

def negativeDomain (a b c : ℝ) : Set ℝ :=
  Set.Ioo
    (-b / (2 * a) - negativeRadius a b c)
    (-b / (2 * a) + negativeRadius a b c)

def negativeCompletedIntegrand (a b c x : ℝ) : ℝ :=
  (1 / Real.sqrt (-a)) /
    Real.sqrt ((negativeRadius a b c) ^ 2 -
      (x + b / (2 * a)) ^ 2)

def negativePrimitive (a b c x : ℝ) : ℝ :=
  (1 / Real.sqrt (-a)) *
    Real.arcsin ((x + b / (2 * a)) / negativeRadius a b c)

def negativeDerivativePrimitive (a b c x : ℝ) : ℝ :=
  (1 / Real.sqrt (-a)) *
    Real.arcsin (-(2 * a * x + b) / Real.sqrt (discriminant a b c))

private theorem add_sqrt_sq_add_pos (x d : ℝ) (hd : 0 < d) :
    0 < x + Real.sqrt (x ^ 2 + d) := by
  have hq : 0 < x ^ 2 + d := by nlinarith [sq_nonneg x]
  have hs : 0 < Real.sqrt (x ^ 2 + d) := Real.sqrt_pos.2 hq
  have hs_sq : (Real.sqrt (x ^ 2 + d)) ^ 2 = x ^ 2 + d :=
    Real.sq_sqrt hq.le
  by_cases hx : 0 ≤ x
  · nlinarith
  · have hx' : x < 0 := lt_of_not_ge hx
    nlinarith

private theorem hasDerivAt_log_add_sqrt_sq_add (d x : ℝ) (hd : 0 < d) :
    HasDerivAt
      (fun y : ℝ => Real.log |y + Real.sqrt (y ^ 2 + d)|)
      (1 / Real.sqrt (x ^ 2 + d)) x := by
  have hq : 0 < x ^ 2 + d := by nlinarith [sq_nonneg x]
  have hs : 0 < Real.sqrt (x ^ 2 + d) := Real.sqrt_pos.2 hq
  have hs_sq : (Real.sqrt (x ^ 2 + d)) ^ 2 = x ^ 2 + d :=
    Real.sq_sqrt hq.le
  have hqder : HasDerivAt (fun y : ℝ => y ^ 2 + d) (2 * x) x := by
    simpa [mul_comm] using ((hasDerivAt_id x).pow 2).add_const d
  have hsder :
      HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 + d))
        (x / Real.sqrt (x ^ 2 + d)) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hqder using 1
    field_simp [ne_of_gt hs]
  have hvder :
      HasDerivAt (fun y : ℝ => y + Real.sqrt (y ^ 2 + d))
        (1 + x / Real.sqrt (x ^ 2 + d)) x :=
    (hasDerivAt_id x).add hsder
  have hv : 0 < x + Real.sqrt (x ^ 2 + d) :=
    add_sqrt_sq_add_pos x d hd
  have hlog := (Real.hasDerivAt_log (ne_of_gt hv)).comp x hvder
  have hfun :
      (fun y : ℝ => Real.log |y + Real.sqrt (y ^ 2 + d)|) =
        fun y : ℝ => Real.log (y + Real.sqrt (y ^ 2 + d)) := by
    funext y
    rw [abs_of_pos (add_sqrt_sq_add_pos y d hd)]
  rw [hfun]
  convert hlog using 1
  field_simp [ne_of_gt hs, ne_of_gt hv] <;> ring

private theorem hasDerivAt_arcsin_div_radius
    (r x : ℝ) (hr : 0 < r) (hleft : -r < x) (hright : x < r) :
    HasDerivAt (fun y : ℝ => Real.arcsin (y / r))
      (1 / Real.sqrt (r ^ 2 - x ^ 2)) x := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hnegone : x / r ≠ (-1 : ℝ) := by
    have h : -1 < x / r := (lt_div_iff₀ hr).2 (by simpa using hleft)
    linarith
  have hone : x / r ≠ (1 : ℝ) := by
    have h : x / r < 1 := (div_lt_iff₀ hr).2 (by simpa using hright)
    linarith
  have hlin : HasDerivAt (fun y : ℝ => y / r) (1 / r) x := by
    convert (hasDerivAt_id x).mul_const (1 / r) using 1 <;>
      simp [div_eq_mul_inv]
  have hcomp := (Real.hasDerivAt_arcsin hnegone hone).comp x hlin
  have hunit : 0 < 1 - (x / r) ^ 2 := by
    have habs : |x| < r := (abs_lt).2 ⟨hleft, hright⟩
    have hsquare : x ^ 2 < r ^ 2 := by
      have hsum : 0 < r + |x| := by nlinarith [abs_nonneg x]
      have hprod : 0 < (r - |x|) * (r + |x|) :=
        mul_pos (sub_pos.mpr habs) hsum
      have habssquare : |x| ^ 2 < r ^ 2 := by
        nlinarith [hprod]
      calc
        x ^ 2 = |x| ^ 2 := (sq_abs x).symm
        _ < r ^ 2 := habssquare
    have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
    have hratio : x ^ 2 / r ^ 2 < 1 :=
      (div_lt_one hr2).2 hsquare
    have hquot : (x / r) ^ 2 = x ^ 2 / r ^ 2 := by
      field_simp [hr0]
    rw [hquot]
    linarith
  have halg : r ^ 2 - x ^ 2 = r ^ 2 * (1 - (x / r) ^ 2) := by
    field_simp [hr0]
  have hsqrt :
      Real.sqrt (r ^ 2 - x ^ 2) =
        r * Real.sqrt (1 - (x / r) ^ 2) := by
    rw [halg, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs,
      abs_of_pos hr]
  convert hcomp using 1
  rw [hsqrt]
  field_simp [hr0, ne_of_gt (Real.sqrt_pos.2 hunit)]

private theorem antiderivatives_eq_primitive_of_open_convex
    (s : Set ℝ) (hsopen : IsOpen s) (hsconv : Convex ℝ s)
    (hsne : s.Nonempty) (g p : ℝ → ℝ)
    (hp : ∀ x ∈ s, HasDerivAt p (g x) x) :
    antiderivativesOn s g = primitiveFamilyOn s p := by
  ext F
  constructor
  · rintro ⟨hFdiff, hFder⟩
    have hD : DifferentiableOn ℝ (fun y => F y - p y) s := by
      intro y hy
      exact (hFdiff y hy).sub (hp y hy).differentiableAt.differentiableWithinAt
    have hz : ∀ y ∈ s, deriv (fun z => F z - p z) y = 0 := by
      intro y hy
      have hFyat : DifferentiableAt ℝ F y :=
        (hFdiff y hy).differentiableAt (hsopen.mem_nhds hy)
      have hpyat : DifferentiableAt ℝ p y := (hp y hy).differentiableAt
      change deriv (F - p) y = 0
      rw [deriv_sub hFyat hpyat, hFder y hy, (hp y hy).deriv]
      ring
    rcases hsne with ⟨x₀, hx₀⟩
    refine ⟨F x₀ - p x₀, ?_⟩
    intro x hx
    have hconst : F x - p x = F x₀ - p x₀ := by
      exact hsopen.is_const_of_deriv_eq_zero hsconv.isPreconnected
        hD hz hx hx₀
    linarith
  · rintro ⟨C, hFC⟩
    have hhas : ∀ x ∈ s, HasDerivAt F (g x) x := by
      intro x hx
      have hevent:
          F =ᶠ[nhds x] (fun y => p y + C) :=
        Filter.Eventually.mono (hsopen.mem_nhds hx) (fun y hy => hFC y hy)
      exact ((hp x hx).add_const C).congr_of_eventuallyEq hevent
    constructor
    · intro x hx
      exact (hhas x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hhas x hx).deriv

private theorem primitiveFamilyOn_eq_of_pointwise_add_const
    (s : Set ℝ) (p q : ℝ → ℝ) (K : ℝ)
    (h : ∀ x ∈ s, p x = q x + K) :
    primitiveFamilyOn s p = primitiveFamilyOn s q := by
  ext F
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨K + C, ?_⟩
    intro x hx
    rw [hC x hx, h x hx]
    ring
  · rintro ⟨C, hC⟩
    refine ⟨C - K, ?_⟩
    intro x hx
    rw [hC x hx, h x hx]
    ring

theorem gap1 (a b c : ℝ) (ha : 0 < a)
    (hdisc : 0 < 4 * a * c - b ^ 2) :
    antiderivativesOn Set.univ (integrand a b c) =
      antiderivativesOn Set.univ (positiveCompletedIntegrand a b c) := by
  apply congrArg (antiderivativesOn Set.univ)
  funext x
  have ha0 : a ≠ 0 := ne_of_gt ha
  have halg :
      quadratic a b c x =
        a * ((x + b / (2 * a)) ^ 2 +
          (4 * a * c - b ^ 2) / (4 * a ^ 2)) := by
    unfold quadratic
    field_simp [ha0]
    ring
  unfold integrand positiveCompletedIntegrand
  rw [halg, Real.sqrt_mul ha.le]
  simp [div_eq_mul_inv, mul_comm]

theorem gap2 (a b c : ℝ) (ha : 0 < a)
    (hdisc : 0 < 4 * a * c - b ^ 2) :
    antiderivativesOn Set.univ (positiveCompletedIntegrand a b c) =
      antiderivativesOn Set.univ
        (fun x => (1 / Real.sqrt a) /
          Real.sqrt ((x + b / (2 * a)) ^ 2 +
            (4 * a * c - b ^ 2) / (4 * a ^ 2))) := by
  rfl

theorem gap3 (a b c : ℝ) (ha : 0 < a)
    (hdisc : 0 < 4 * a * c - b ^ 2) :
    antiderivativesOn Set.univ
        (fun x => (1 / Real.sqrt a) /
          Real.sqrt ((x + b / (2 * a)) ^ 2 +
            (4 * a * c - b ^ 2) / (4 * a ^ 2))) =
      antiderivativesOn Set.univ (positiveCompletedIntegrand a b c) := by
  rfl

theorem gap4 (a b c : ℝ) (ha : 0 < a)
    (hdisc : 0 < 4 * a * c - b ^ 2) :
    antiderivativesOn Set.univ (positiveCompletedIntegrand a b c) =
      primitiveFamilyOn Set.univ (positivePrimitive a b c) := by
  apply antiderivatives_eq_primitive_of_open_convex
    Set.univ isOpen_univ convex_univ Set.univ_nonempty
  intro x hx
  have ha0 : a ≠ 0 := ne_of_gt ha
  let d : ℝ := (4 * a * c - b ^ 2) / (4 * a ^ 2)
  have hd : 0 < d := by
    dsimp [d]
    exact div_pos hdisc (by positivity)
  have hq : ∀ y : ℝ,
      y ^ 2 + (b / a) * y + c / a =
        (y + b / (2 * a)) ^ 2 + d := by
    intro y
    dsimp [d]
    field_simp [ha0]
    ring
  have hbase :=
    hasDerivAt_log_add_sqrt_sq_add d (x + b / (2 * a)) hd
  have hshift :
      HasDerivAt (fun y : ℝ => y + b / (2 * a)) 1 x := by
    simpa using (hasDerivAt_id x).add_const (b / (2 * a))
  have hcomp := hbase.comp x hshift
  have hscaled := hcomp.const_mul (1 / Real.sqrt a)
  dsimp [d] at hscaled
  convert hscaled using 1
  · funext y
    unfold positivePrimitive
    rw [hq y]
  · unfold positiveCompletedIntegrand
    simp [div_eq_mul_inv, mul_comm]

theorem gap5 (a b c : ℝ) (ha : 0 < a)
    (hdisc : 0 < 4 * a * c - b ^ 2) :
    primitiveFamilyOn Set.univ (positivePrimitive a b c) =
      primitiveFamilyOn Set.univ (positiveDerivativePrimitive a b c) := by
  apply primitiveFamilyOn_eq_of_pointwise_add_const
    (K := -(1 / Real.sqrt a) * Real.log a)
  intro x hx
  have ha0 : a ≠ 0 := ne_of_gt ha
  let d : ℝ := (4 * a * c - b ^ 2) / (4 * a ^ 2)
  let u : ℝ := x + b / (2 * a)
  have hd : 0 < d := by
    dsimp [d]
    exact div_pos hdisc (by positivity)
  have hnorm :
      x ^ 2 + (b / a) * x + c / a = u ^ 2 + d := by
    dsimp [u, d]
    field_simp [ha0]
    ring
  have hraw : quadratic a b c x = a * (u ^ 2 + d) := by
    unfold quadratic
    rw [← hnorm]
    field_simp [ha0]
  have hsqrt :
      Real.sqrt (a * quadratic a b c x) =
        a * Real.sqrt (u ^ 2 + d) := by
    rw [hraw]
    have halg : a * (a * (u ^ 2 + d)) = a ^ 2 * (u ^ 2 + d) := by ring
    rw [halg, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs,
      abs_of_pos ha]
  have hinside :
      (2 * a * x + b) / 2 + Real.sqrt (a * quadratic a b c x) =
        a * (u + Real.sqrt (u ^ 2 + d)) := by
    rw [hsqrt]
    dsimp [u]
    field_simp [ha0]
  have huv : 0 < u + Real.sqrt (u ^ 2 + d) :=
    add_sqrt_sq_add_pos u d hd
  have hlog :
      Real.log |(2 * a * x + b) / 2 +
          Real.sqrt (a * quadratic a b c x)| =
        Real.log a + Real.log |u + Real.sqrt (u ^ 2 + d)| := by
    rw [hinside, abs_mul, abs_of_pos ha,
      Real.log_mul (ne_of_gt ha) (abs_ne_zero.mpr (ne_of_gt huv))]
  unfold positivePrimitive positiveDerivativePrimitive
  rw [hnorm, hlog]
  dsimp [u]
  ring

theorem gap6 (a b c : ℝ) (ha : 0 < a)
    (hdisc : 0 < 4 * a * c - b ^ 2) :
    antiderivativesOn Set.univ (integrand a b c) =
      primitiveFamilyOn Set.univ (positiveDerivativePrimitive a b c) := by
  calc
    antiderivativesOn Set.univ (integrand a b c) =
        antiderivativesOn Set.univ (positiveCompletedIntegrand a b c) :=
      gap1 a b c ha hdisc
    _ = primitiveFamilyOn Set.univ (positivePrimitive a b c) :=
      gap4 a b c ha hdisc
    _ = primitiveFamilyOn Set.univ (positiveDerivativePrimitive a b c) :=
      gap5 a b c ha hdisc

theorem gap7 (a b c : ℝ) (ha : a < 0)
    (hdisc : 0 < discriminant a b c) :
    antiderivativesOn (negativeDomain a b c) (integrand a b c) =
      antiderivativesOn (negativeDomain a b c)
        (negativeCompletedIntegrand a b c) := by
  apply congrArg (antiderivativesOn (negativeDomain a b c))
  funext x
  have ha0 : a ≠ 0 := ne_of_lt ha
  have hneg : 0 < -a := neg_pos.mpr ha
  have hsqd : (Real.sqrt (discriminant a b c)) ^ 2 =
      discriminant a b c := Real.sq_sqrt hdisc.le
  have halg :
      quadratic a b c x =
        (-a) * ((negativeRadius a b c) ^ 2 -
          (x + b / (2 * a)) ^ 2) := by
    unfold quadratic negativeRadius
    field_simp [ha0]
    rw [hsqd]
    unfold discriminant
    ring
  unfold integrand negativeCompletedIntegrand
  rw [halg, Real.sqrt_mul hneg.le]
  simp [div_eq_mul_inv, mul_comm]

theorem gap8 (a b c : ℝ) (ha : a < 0)
    (hdisc : 0 < discriminant a b c) :
    antiderivativesOn (negativeDomain a b c)
        (negativeCompletedIntegrand a b c) =
      antiderivativesOn (negativeDomain a b c)
        (fun x => (1 / Real.sqrt (-a)) /
          Real.sqrt ((negativeRadius a b c) ^ 2 -
            (x + b / (2 * a)) ^ 2)) := by
  rfl

theorem gap9 (a b c : ℝ) (ha : a < 0)
    (hdisc : 0 < discriminant a b c) :
    antiderivativesOn (negativeDomain a b c)
        (fun x => (1 / Real.sqrt (-a)) /
          Real.sqrt ((negativeRadius a b c) ^ 2 -
            (x + b / (2 * a)) ^ 2)) =
      antiderivativesOn (negativeDomain a b c)
        (negativeCompletedIntegrand a b c) := by
  rfl

theorem gap10 (a b c : ℝ) (ha : a < 0)
    (hdisc : 0 < discriminant a b c) :
    antiderivativesOn (negativeDomain a b c)
        (negativeCompletedIntegrand a b c) =
      primitiveFamilyOn (negativeDomain a b c) (negativePrimitive a b c) := by
  apply antiderivatives_eq_primitive_of_open_convex
    (negativeDomain a b c)
  · unfold negativeDomain
    exact isOpen_Ioo
  · unfold negativeDomain
    exact convex_Ioo _ _
  · unfold negativeDomain
    have hr : 0 < negativeRadius a b c := by
      unfold negativeRadius
      exact div_pos (Real.sqrt_pos.2 hdisc) (by nlinarith)
    exact Set.nonempty_Ioo.2 (by linarith)
  · intro x hx
    have hr : 0 < negativeRadius a b c := by
      unfold negativeRadius
      exact div_pos (Real.sqrt_pos.2 hdisc) (by nlinarith)
    have hbounds :
        -negativeRadius a b c < x + b / (2 * a) ∧
          x + b / (2 * a) < negativeRadius a b c := by
      unfold negativeDomain at hx
      constructor
      · calc
          -negativeRadius a b c =
              (-b / (2 * a) - negativeRadius a b c) + b / (2 * a) := by ring
          _ < x + b / (2 * a) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              (add_lt_add_right hx.1 (b / (2 * a)))
      · calc
          x + b / (2 * a) <
              (-b / (2 * a) + negativeRadius a b c) + b / (2 * a) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              (add_lt_add_right hx.2 (b / (2 * a)))
          _ = negativeRadius a b c := by ring
    have hbase := hasDerivAt_arcsin_div_radius
      (negativeRadius a b c) (x + b / (2 * a)) hr
      hbounds.1 hbounds.2
    have hshift :
        HasDerivAt (fun y : ℝ => y + b / (2 * a)) 1 x := by
      simpa using (hasDerivAt_id x).add_const (b / (2 * a))
    have hcomp := hbase.comp x hshift
    have hscaled := hcomp.const_mul (1 / Real.sqrt (-a))
    convert hscaled using 1
    unfold negativeCompletedIntegrand
    simp [div_eq_mul_inv, mul_comm]

theorem gap11 (a b c : ℝ) (ha : a < 0)
    (hdisc : 0 < discriminant a b c) :
    primitiveFamilyOn (negativeDomain a b c) (negativePrimitive a b c) =
      primitiveFamilyOn (negativeDomain a b c)
        (negativeDerivativePrimitive a b c) := by
  apply congrArg (primitiveFamilyOn (negativeDomain a b c))
  funext x
  have ha0 : a ≠ 0 := ne_of_lt ha
  have hsqrt : Real.sqrt (discriminant a b c) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hdisc)
  have harg :
      (x + b / (2 * a)) / negativeRadius a b c =
        -(2 * a * x + b) / Real.sqrt (discriminant a b c) := by
    unfold negativeRadius
    field_simp [ha0, hsqrt]
  unfold negativePrimitive negativeDerivativePrimitive
  rw [harg]

theorem gap12 (a b c : ℝ) (ha : a < 0)
    (hdisc : 0 < discriminant a b c) :
    antiderivativesOn (negativeDomain a b c) (integrand a b c) =
      primitiveFamilyOn (negativeDomain a b c)
        (negativeDerivativePrimitive a b c) := by
  calc
    antiderivativesOn (negativeDomain a b c) (integrand a b c) =
        antiderivativesOn (negativeDomain a b c)
          (negativeCompletedIntegrand a b c) := gap7 a b c ha hdisc
    _ = primitiveFamilyOn (negativeDomain a b c)
          (negativePrimitive a b c) := gap10 a b c ha hdisc
    _ = primitiveFamilyOn (negativeDomain a b c)
          (negativeDerivativePrimitive a b c) := gap11 a b c ha hdisc

end

end ProofGap.Exercise1850
