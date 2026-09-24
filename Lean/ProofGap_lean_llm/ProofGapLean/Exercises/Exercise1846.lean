import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1846

noncomputable section

def integrand (a b x : ℝ) : ℝ := 1 / Real.sqrt (a + b * x ^ 2)

def antiderivativesOn (s : Set ℝ) (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F s ∧ ∀ x ∈ s, deriv F x = g x}

def primitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}

def logPrimitive (a b x : ℝ) : ℝ :=
  (1 / Real.sqrt b) *
    Real.log |x * Real.sqrt b + Real.sqrt (a + b * x ^ 2)|

def asinPrimitive (a b x : ℝ) : ℝ :=
  (1 / Real.sqrt (-b)) *
    Real.arcsin (x * Real.sqrt ((-b) / a))

def boundedDomain (a b : ℝ) : Set ℝ :=
  Set.Ioo (-Real.sqrt (a / (-b))) (Real.sqrt (a / (-b)))

private theorem antiderivatives_eq_primitive
    (s : Set ℝ) (g p : ℝ → ℝ)
    (hsopen : IsOpen s) (hsconn : IsPreconnected s) (hsne : s.Nonempty)
    (hp : ∀ x ∈ s, HasDerivAt p (g x) x) :
    antiderivativesOn s g = primitiveFamilyOn s p := by
  ext F
  constructor
  · rintro ⟨hF, hder⟩
    obtain ⟨x₀, hx₀⟩ := hsne
    refine ⟨F x₀ - p x₀, ?_⟩
    have hdiff : DifferentiableOn ℝ (fun x => F x - p x) s := by
      intro x hx
      exact (hF x hx).sub (hp x hx).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ s, deriv (fun y => F y - p y) x = 0 := by
      intro x hx
      have hFa : DifferentiableAt ℝ F x :=
        (hF x hx).differentiableAt (hsopen.mem_nhds hx)
      have hFd : HasDerivAt F (g x) x := by
        have hd := hFa.hasDerivAt
        rw [hder x hx] at hd
        exact hd
      simpa using (hFd.sub (hp x hx)).deriv
    intro x hx
    have hc :=
      hsopen.is_const_of_deriv_eq_zero hsconn hdiff hzero hx hx₀
    change F x - p x = F x₀ - p x₀ at hc
    linarith
  · rintro ⟨C, hC⟩
    constructor
    · intro x hx
      have heq : F =ᶠ[nhds x] fun y => p y + C := by
        filter_upwards [hsopen.mem_nhds hx] with y hy
        exact hC y hy
      have hFp : HasDerivAt F (g x) x :=
        ((hp x hx).add_const C).congr_of_eventuallyEq heq
      exact hFp.differentiableAt.differentiableWithinAt
    · intro x hx
      have heq : F =ᶠ[nhds x] fun y => p y + C := by
        filter_upwards [hsopen.mem_nhds hx] with y hy
        exact hC y hy
      have hFp : HasDerivAt F (g x) x :=
        ((hp x hx).add_const C).congr_of_eventuallyEq heq
      exact hFp.deriv

private theorem log_inner_pos (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 < x * Real.sqrt b + Real.sqrt (a + b * x ^ 2) := by
  have hr : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hs : 0 ≤ Real.sqrt (a + b * x ^ 2) := Real.sqrt_nonneg _
  have hr2 : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb.le
  have hq : 0 < a + b * x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hs2 : (Real.sqrt (a + b * x ^ 2)) ^ 2 = a + b * x ^ 2 :=
    Real.sq_sqrt hq.le
  have hxr2 : (x * Real.sqrt b) ^ 2 = b * x ^ 2 := by
    rw [mul_pow, hr2]
    ring
  nlinarith [sq_nonneg (Real.sqrt (a + b * x ^ 2) + x * Real.sqrt b)]

private theorem hasDerivAt_logPrimitive
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    HasDerivAt (logPrimitive a b) (integrand a b x) x := by
  have hq : 0 < a + b * x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hr : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hs : 0 < Real.sqrt (a + b * x ^ 2) := Real.sqrt_pos.2 hq
  have hu : 0 < x * Real.sqrt b + Real.sqrt (a + b * x ^ 2) :=
    log_inner_pos a b x ha hb
  have hqder : HasDerivAt (fun y : ℝ => a + b * y ^ 2) (2 * b * x) x := by
    convert (((hasDerivAt_id x).pow 2).const_mul b).const_add a using 1 <;>
      simp only [id_eq] <;> ring
  have hsder : HasDerivAt (fun y : ℝ => Real.sqrt (a + b * y ^ 2))
      (b * x / Real.sqrt (a + b * x ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt hq.ne').comp x hqder using 1 <;>
      field_simp [hs.ne'] <;> ring
  have huder : HasDerivAt
      (fun y : ℝ => y * Real.sqrt b + Real.sqrt (a + b * y ^ 2))
      (Real.sqrt b + b * x / Real.sqrt (a + b * x ^ 2)) x := by
    simpa using ((hasDerivAt_id x).mul_const (Real.sqrt b)).add hsder
  have hlog : HasDerivAt
      (fun y : ℝ => Real.log (y * Real.sqrt b + Real.sqrt (a + b * y ^ 2)))
      ((Real.sqrt b + b * x / Real.sqrt (a + b * x ^ 2)) /
        (x * Real.sqrt b + Real.sqrt (a + b * x ^ 2))) x := by
    simpa [Function.comp_apply, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_log hu.ne').comp x huder
  have hfun : logPrimitive a b =
      fun y => (1 / Real.sqrt b) *
        Real.log (y * Real.sqrt b + Real.sqrt (a + b * y ^ 2)) := by
    funext y
    simp only [logPrimitive]
    rw [abs_of_pos (log_inner_pos a b y ha hb)]
  rw [hfun]
  have hscaled := hlog.const_mul (1 / Real.sqrt b)
  have hinner :
      (Real.sqrt b + b * x / Real.sqrt (a + b * x ^ 2)) /
          (x * Real.sqrt b + Real.sqrt (a + b * x ^ 2)) =
        Real.sqrt b / Real.sqrt (a + b * x ^ 2) := by
    apply (div_eq_iff hu.ne').2
    field_simp [hs.ne'] <;> nlinarith [Real.sq_sqrt hb.le]
  have hcoef :
      (1 / Real.sqrt b) *
          ((Real.sqrt b + b * x / Real.sqrt (a + b * x ^ 2)) /
            (x * Real.sqrt b + Real.sqrt (a + b * x ^ 2))) =
        integrand a b x := by
    rw [integrand, hinner]
    field_simp [hr.ne', hs.ne'] <;> ring
  rw [hcoef] at hscaled
  exact hscaled

private theorem bounded_normalization
    (a b : ℝ) (ha : 0 < a) (hb : b < 0) (x : ℝ)
    (hx : x ∈ boundedDomain a b) :
    0 < 1 - (x * Real.sqrt ((-b) / a)) ^ 2 ∧
      integrand a b x =
        (1 / Real.sqrt a) /
          Real.sqrt (1 - (x * Real.sqrt ((-b) / a)) ^ 2) := by
  have hc : 0 < -b := neg_pos.mpr hb
  have hab : 0 < a / (-b) := div_pos ha hc
  have hba : 0 < (-b) / a := div_pos hc ha
  have hr : 0 < Real.sqrt (a / (-b)) := Real.sqrt_pos.2 hab
  have hr2 : (Real.sqrt (a / (-b))) ^ 2 = a / (-b) :=
    Real.sq_sqrt hab.le
  have hxI : -Real.sqrt (a / (-b)) < x ∧ x < Real.sqrt (a / (-b)) := hx
  have hx2 : x ^ 2 < a / (-b) := by
    nlinarith [sq_nonneg (x + Real.sqrt (a / (-b))),
      sq_nonneg (x - Real.sqrt (a / (-b)))]
  have hcross : x ^ 2 * (-b) < a := by
    have h := mul_lt_mul_of_pos_right hx2 hc
    rw [div_mul_cancel₀ a hc.ne'] at h
    exact h
  have hu2 : (x * Real.sqrt ((-b) / a)) ^ 2 = x ^ 2 * ((-b) / a) := by
    rw [mul_pow, Real.sq_sqrt hba.le]
  have hult : (x * Real.sqrt ((-b) / a)) ^ 2 < 1 := by
    rw [hu2]
    calc
      x ^ 2 * ((-b) / a) = (x ^ 2 * (-b)) / a := by
        field_simp [ha.ne']
      _ < 1 := (div_lt_iff₀ ha).2 (by simpa using hcross)
  have ht : 0 < 1 - (x * Real.sqrt ((-b) / a)) ^ 2 := by
    linarith
  refine ⟨ht, ?_⟩
  have hrad : a + b * x ^ 2 =
      a * (1 - (x * Real.sqrt ((-b) / a)) ^ 2) := by
    rw [hu2]
    field_simp [ha.ne'] <;> ring
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hst : Real.sqrt (1 - (x * Real.sqrt ((-b) / a)) ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 ht).ne'
  rw [integrand, hrad, Real.sqrt_mul ha.le]
  field_simp [hsa, hst]

private theorem hasDerivAt_asinPrimitive
    (a b : ℝ) (ha : 0 < a) (hb : b < 0) (x : ℝ)
    (hx : x ∈ boundedDomain a b) :
    HasDerivAt (asinPrimitive a b)
      ((1 / Real.sqrt a) /
        Real.sqrt (1 - (x * Real.sqrt ((-b) / a)) ^ 2)) x := by
  have hc : 0 < -b := neg_pos.mpr hb
  have hba : 0 < (-b) / a := div_pos hc ha
  have ht := (bounded_normalization a b ha hb x hx).1
  have hu2 : (x * Real.sqrt ((-b) / a)) ^ 2 < 1 := by
    linarith
  have hu : x * Real.sqrt ((-b) / a) ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor <;>
      nlinarith [sq_nonneg (x * Real.sqrt ((-b) / a) - 1),
        sq_nonneg (x * Real.sqrt ((-b) / a) + 1)]
  have hlin : HasDerivAt (fun y : ℝ => y * Real.sqrt ((-b) / a))
      (Real.sqrt ((-b) / a)) x := by
    simpa using (hasDerivAt_id x).mul_const (Real.sqrt ((-b) / a))
  have hneg : x * Real.sqrt ((-b) / a) ≠ -1 := ne_of_gt hu.1
  have hone : x * Real.sqrt ((-b) / a) ≠ 1 := ne_of_lt hu.2
  have harc : HasDerivAt
      (fun y : ℝ => Real.arcsin (y * Real.sqrt ((-b) / a)))
      ((1 / Real.sqrt (1 - (x * Real.sqrt ((-b) / a)) ^ 2)) *
        Real.sqrt ((-b) / a)) x := by
    simpa [Function.comp_apply] using
      (Real.hasDerivAt_arcsin hneg hone).comp x hlin
  have hprod : Real.sqrt ((-b) / a) * Real.sqrt a = Real.sqrt (-b) := by
    calc
      Real.sqrt ((-b) / a) * Real.sqrt a =
          Real.sqrt (((-b) / a) * a) :=
        (Real.sqrt_mul (div_nonneg hc.le ha.le) a).symm
      _ = Real.sqrt (-b) := by rw [div_mul_cancel₀ (-b) ha.ne']
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hsb : Real.sqrt (-b) ≠ 0 := (Real.sqrt_pos.2 hc).ne'
  have hratio :
      (1 / Real.sqrt (-b)) * Real.sqrt ((-b) / a) =
        1 / Real.sqrt a := by
    calc
      (1 / Real.sqrt (-b)) * Real.sqrt ((-b) / a) =
          Real.sqrt ((-b) / a) / Real.sqrt (-b) := by ring
      _ = 1 / Real.sqrt a := by
        apply (div_eq_iff hsb).2
        calc
          Real.sqrt ((-b) / a) = Real.sqrt (-b) / Real.sqrt a :=
            (eq_div_iff hsa).2 hprod
          _ = (1 / Real.sqrt a) * Real.sqrt (-b) := by ring
  have hcoef :
      (1 / Real.sqrt (-b)) *
          ((1 / Real.sqrt (1 - (x * Real.sqrt ((-b) / a)) ^ 2)) *
            Real.sqrt ((-b) / a)) =
        (1 / Real.sqrt a) /
          Real.sqrt (1 - (x * Real.sqrt ((-b) / a)) ^ 2) := by
    calc
      (1 / Real.sqrt (-b)) *
          ((1 / Real.sqrt (1 - (x * Real.sqrt ((-b) / a)) ^ 2)) *
            Real.sqrt ((-b) / a)) =
          ((1 / Real.sqrt (-b)) * Real.sqrt ((-b) / a)) /
            Real.sqrt (1 - (x * Real.sqrt ((-b) / a)) ^ 2) := by ring
      _ = (1 / Real.sqrt a) /
          Real.sqrt (1 - (x * Real.sqrt ((-b) / a)) ^ 2) := by rw [hratio]
  change HasDerivAt
    (fun y : ℝ => (1 / Real.sqrt (-b)) *
      Real.arcsin (y * Real.sqrt ((-b) / a)))
    ((1 / Real.sqrt a) /
      Real.sqrt (1 - (x * Real.sqrt ((-b) / a)) ^ 2)) x
  have hscaled := harc.const_mul (1 / Real.sqrt (-b))
  rw [hcoef] at hscaled
  exact hscaled

theorem gap1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    antiderivativesOn Set.univ (integrand a b) =
      primitiveFamilyOn Set.univ (logPrimitive a b) := by
  apply antiderivatives_eq_primitive
  · exact isOpen_univ
  · exact isPreconnected_univ
  · exact Set.univ_nonempty
  · intro x hx
    exact hasDerivAt_logPrimitive a b ha hb x

theorem gap2 (a b : ℝ) (ha : 0 < a) (hb : b < 0) :
    antiderivativesOn (boundedDomain a b) (integrand a b) =
      antiderivativesOn (boundedDomain a b)
        (fun x => (1 / Real.sqrt a) /
          Real.sqrt (1 - (x * Real.sqrt ((-b) / a)) ^ 2)) := by
  ext F
  constructor
  · rintro ⟨hF, hder⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = integrand a b x := hder x hx
      _ = (1 / Real.sqrt a) /
          Real.sqrt (1 - (x * Real.sqrt ((-b) / a)) ^ 2) :=
        (bounded_normalization a b ha hb x hx).2
  · rintro ⟨hF, hder⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = (1 / Real.sqrt a) /
          Real.sqrt (1 - (x * Real.sqrt ((-b) / a)) ^ 2) := hder x hx
      _ = integrand a b x :=
        (bounded_normalization a b ha hb x hx).2.symm

theorem gap3 (a b : ℝ) (ha : 0 < a) (hb : b < 0) :
    antiderivativesOn (boundedDomain a b)
        (fun x => (1 / Real.sqrt a) /
          Real.sqrt (1 - (x * Real.sqrt ((-b) / a)) ^ 2)) =
      primitiveFamilyOn (boundedDomain a b) (asinPrimitive a b) := by
  apply antiderivatives_eq_primitive
  · exact isOpen_Ioo
  · exact isPreconnected_Ioo
  · have hr : 0 < Real.sqrt (a / (-b)) :=
      Real.sqrt_pos.2 (div_pos ha (neg_pos.mpr hb))
    refine ⟨(0 : ℝ), ?_⟩
    change -Real.sqrt (a / (-b)) < (0 : ℝ) ∧
      (0 : ℝ) < Real.sqrt (a / (-b))
    exact ⟨neg_neg_of_pos hr, hr⟩
  · intro x hx
    exact hasDerivAt_asinPrimitive a b ha hb x hx

theorem gap4 (a b : ℝ) (ha : 0 < a) (hb : b < 0) :
    antiderivativesOn (boundedDomain a b) (integrand a b) =
      primitiveFamilyOn (boundedDomain a b) (asinPrimitive a b) := by
  exact (gap2 a b ha hb).trans (gap3 a b ha hb)

end

end ProofGap.Exercise1846
