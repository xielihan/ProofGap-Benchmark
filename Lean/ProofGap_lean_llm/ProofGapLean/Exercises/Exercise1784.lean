import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1784

noncomputable section

def angle (a b x : ℝ) : ℝ :=
  Real.arcsin (Real.sqrt ((x - a) / (b - a)))
def integrand (a b x : ℝ) : ℝ :=
  1 / Real.sqrt ((x - a) * (b - x))
def primitive (a b x : ℝ) : ℝ :=
  2 * Real.arcsin (Real.sqrt ((x - a) / (b - a)))
def domain (a b : ℝ) : Set ℝ := Set.Ioo a b
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem angle_differentiableAt (a b x : ℝ)
    (hx : x ∈ domain a b) : DifferentiableAt ℝ (angle a b) x := by
  have hx' : x ∈ Set.Ioo a b := by simpa [domain] using hx
  have hab : a < b := lt_trans hx'.1 hx'.2
  have hd : 0 < b - a := sub_pos.mpr hab
  have hp : 0 < x - a := sub_pos.mpr hx'.1
  have hu : 0 < (x - a) / (b - a) := div_pos hp hd
  have hu1 : (x - a) / (b - a) < 1 := by
    apply (div_lt_one hd).2
    linarith [hx'.2]
  have hs0 := Real.sqrt_nonneg ((x - a) / (b - a))
  have hssq := Real.sq_sqrt (le_of_lt hu)
  have hslo : -1 < Real.sqrt ((x - a) / (b - a)) := by
    have := Real.sqrt_pos.2 hu
    linarith
  have hshi : Real.sqrt ((x - a) / (b - a)) < 1 := by
    nlinarith
  have hquot : HasDerivAt (fun y : ℝ => (y - a) / (b - a))
      (1 / (b - a)) x := by
    simpa using ((hasDerivAt_id x).sub_const a).div_const (b - a)
  have hsqrt :=
    (Real.hasDerivAt_sqrt (ne_of_gt hu)).comp x hquot
  have harcsin :=
    (Real.hasDerivAt_arcsin (ne_of_gt hslo) (ne_of_lt hshi)).comp x hsqrt
  simpa only [angle, Function.comp_def] using harcsin.differentiableAt

theorem gap1 (a b x : ℝ) (hx : x ∈ domain a b) :
    a < x := by
  simpa [domain] using hx.1

theorem gap2 (a b x : ℝ) (hx : x ∈ domain a b) :
    x < b := by
  simpa [domain] using hx.2

theorem gap3 (a b x : ℝ) (hx : x ∈ domain a b) :
    a < b := by
  exact lt_trans (gap1 a b x hx) (gap2 a b x hx)

theorem gap4 (a b x : ℝ) (hx : x ∈ domain a b) :
    Real.sqrt ((x - a) * (b - x)) =
      (b - a) * Real.sin (angle a b x) * Real.cos (angle a b x) := by
  have hax : a < x := gap1 a b x hx
  have hxb : x < b := gap2 a b x hx
  have hab : a < b := gap3 a b x hx
  have hd : 0 < b - a := sub_pos.mpr hab
  have hp : 0 < x - a := sub_pos.mpr hax
  have hq : 0 < b - x := sub_pos.mpr hxb
  have hu : 0 < (x - a) / (b - a) := div_pos hp hd
  have hu1 : (x - a) / (b - a) < 1 := by
    apply (div_lt_one hd).2
    linarith
  have hsu : Real.sqrt ((x - a) / (b - a)) ^ 2 =
      (x - a) / (b - a) :=
    Real.sq_sqrt (le_of_lt hu)
  have hslo : -1 ≤ Real.sqrt ((x - a) / (b - a)) := by
    have := Real.sqrt_nonneg ((x - a) / (b - a))
    linarith
  have hshi : Real.sqrt ((x - a) / (b - a)) ≤ 1 := by
    have hs0 := Real.sqrt_nonneg ((x - a) / (b - a))
    nlinarith
  rw [angle, Real.sin_arcsin hslo hshi, Real.cos_arcsin, hsu]
  have hl : Real.sqrt ((x - a) * (b - x)) ^ 2 =
      (x - a) * (b - x) :=
    Real.sq_sqrt (mul_nonneg (le_of_lt hp) (le_of_lt hq))
  have hv : 0 ≤ 1 - (x - a) / (b - a) := by linarith
  have hr :
      ((b - a) * Real.sqrt ((x - a) / (b - a)) *
        Real.sqrt (1 - (x - a) / (b - a))) ^ 2 =
        (x - a) * (b - x) := by
    calc
      ((b - a) * Real.sqrt ((x - a) / (b - a)) *
          Real.sqrt (1 - (x - a) / (b - a))) ^ 2 =
          (b - a) ^ 2 *
            (Real.sqrt ((x - a) / (b - a))) ^ 2 *
            (Real.sqrt (1 - (x - a) / (b - a))) ^ 2 := by ring
      _ = (b - a) ^ 2 * ((x - a) / (b - a)) *
            (1 - (x - a) / (b - a)) := by
              rw [Real.sq_sqrt (le_of_lt hu), Real.sq_sqrt hv]
      _ = (x - a) * (b - x) := by
              field_simp [ne_of_gt hd]
              <;> ring
  have hlnonneg : 0 ≤ Real.sqrt ((x - a) * (b - x)) :=
    Real.sqrt_nonneg _
  have hrnonneg :
      0 ≤ (b - a) * Real.sqrt ((x - a) / (b - a)) *
        Real.sqrt (1 - (x - a) / (b - a)) := by positivity
  nlinarith

theorem gap5 (a b x : ℝ) (hx : x ∈ domain a b) :
    1 = 2 * (b - a) * Real.sin (angle a b x) *
      Real.cos (angle a b x) * deriv (angle a b) x := by
  have hx' : x ∈ Set.Ioo a b := by simpa [domain] using hx
  have hab : a < b := gap3 a b x hx
  have hd : 0 < b - a := sub_pos.mpr hab
  have hangle := (angle_differentiableAt a b x hx).hasDerivAt
  have hsin : HasDerivAt (fun y => Real.sin (angle a b y))
      (Real.cos (angle a b x) * deriv (angle a b) x) x :=
    (Real.hasDerivAt_sin (angle a b x)).comp x hangle
  have hprod := hsin.mul hsin
  have hquot : HasDerivAt (fun y : ℝ => (y - a) / (b - a))
      (1 / (b - a)) x := by
    simpa using ((hasDerivAt_id x).sub_const a).div_const (b - a)
  have hnhds : Set.Ioo a b ∈ nhds x :=
    IsOpen.mem_nhds isOpen_Ioo hx'
  have heq :
      (fun y => Real.sin (angle a b y) * Real.sin (angle a b y)) =ᶠ[nhds x]
        (fun y => (y - a) / (b - a)) := by
    filter_upwards [hnhds] with y hy
    have hdy : 0 < b - a := hd
    have hpy : 0 < y - a := sub_pos.mpr hy.1
    have huy : 0 < (y - a) / (b - a) := div_pos hpy hdy
    have huy1 : (y - a) / (b - a) < 1 := by
      apply (div_lt_one hdy).2
      linarith [hy.2]
    have hs0 := Real.sqrt_nonneg ((y - a) / (b - a))
    have hssq := Real.sq_sqrt (le_of_lt huy)
    have hslo : -1 ≤ Real.sqrt ((y - a) / (b - a)) := by linarith
    have hshi : Real.sqrt ((y - a) / (b - a)) ≤ 1 := by nlinarith
    rw [angle, Real.sin_arcsin hslo hshi]
    simpa [pow_two] using hssq
  have hderivEq := heq.deriv_eq
  have hprodDeriv :
      deriv (fun y => Real.sin (angle a b y) * Real.sin (angle a b y)) x =
        Real.cos (angle a b x) * deriv (angle a b) x *
            Real.sin (angle a b x) +
          Real.sin (angle a b x) *
            (Real.cos (angle a b x) * deriv (angle a b) x) := by
    simpa only [Pi.mul_apply] using hprod.deriv
  have hquotDeriv :
      deriv (fun y : ℝ => (y - a) / (b - a)) x = 1 / (b - a) :=
    hquot.deriv
  rw [hprodDeriv, hquotDeriv] at hderivEq
  field_simp [ne_of_gt hd] at hderivEq
  nlinarith

theorem gap6 (a b x : ℝ) (hx : x ∈ domain a b) :
    integrand a b x = 2 * deriv (angle a b) x := by
  have hp : 0 < x - a := sub_pos.mpr (gap1 a b x hx)
  have hq : 0 < b - x := sub_pos.mpr (gap2 a b x hx)
  have hspos : 0 < Real.sqrt ((x - a) * (b - x)) :=
    Real.sqrt_pos.2 (mul_pos hp hq)
  have hsne : Real.sqrt ((x - a) * (b - x)) ≠ 0 := ne_of_gt hspos
  have h := gap5 a b x hx
  have h' :
      1 = 2 * ((b - a) * Real.sin (angle a b x) *
        Real.cos (angle a b x)) * deriv (angle a b) x := by
    calc
      1 = 2 * (b - a) * Real.sin (angle a b x) *
          Real.cos (angle a b x) * deriv (angle a b) x := h
      _ = 2 * ((b - a) * Real.sin (angle a b x) *
          Real.cos (angle a b x)) * deriv (angle a b) x := by ring
  rw [← gap4 a b x hx] at h'
  unfold integrand
  apply (div_eq_iff hsne).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using h'

theorem gap7 (a b x : ℝ) (hx : x ∈ domain a b) :
    HasDerivAt (fun y => 2 * angle a b y) (integrand a b x) x := by
  have h := (angle_differentiableAt a b x hx).hasDerivAt.const_mul 2
  simpa [gap6 a b x hx] using h

theorem gap8 (a b x : ℝ) :
    2 * angle a b x = primitive a b x := by
  rfl

theorem gap9 (a b : ℝ) (hab : a < b) :
    Family (integrand a b) (domain a b) =
      Translates (primitive a b) (domain a b) := by
  ext F
  constructor
  · intro hF
    have hF' : IsAntiderivativeOn F (integrand a b) (domain a b) := hF
    let c : ℝ := (a + b) / 2
    have hc : c ∈ domain a b := by
      simp only [c, domain, Set.mem_Ioo]
      constructor <;> linarith
    have hzero : ∀ x ∈ domain a b,
        HasDerivAt (fun y => F y - primitive a b y) 0 x := by
      intro x hx
      have hP : HasDerivAt (primitive a b) (integrand a b x) x := by
        simpa [primitive, angle] using gap7 a b x hx
      simpa using (hF' x hx).sub hP
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive a b y)
        (Set.Ioo a b) := by
      intro x hx
      exact (hzero x (by simpa [domain] using hx)).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ Set.Ioo a b,
        deriv (fun y => F y - primitive a b y) x = 0 := by
      intro x hx
      exact (hzero x (by simpa [domain] using hx)).deriv
    refine ⟨F c - primitive a b c, ?_⟩
    intro x hx
    have hx' : x ∈ Set.Ioo a b := by simpa [domain] using hx
    have hc' : c ∈ Set.Ioo a b := by simpa [domain] using hc
    have heq : F x - primitive a b x = F c - primitive a b c := by
      exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hdiff hderiv (x := x) (y := c) hx' hc'
    linarith
  · rintro ⟨C, hF⟩
    intro x hx
    have hP : HasDerivAt (primitive a b) (integrand a b x) x := by
      simpa [primitive, angle] using gap7 a b x hx
    have hmodel : HasDerivAt (fun y => primitive a b y + C)
        (integrand a b x) x := hP.add_const C
    have hx' : x ∈ Set.Ioo a b := by simpa [domain] using hx
    have hnhds : Set.Ioo a b ∈ nhds x :=
      IsOpen.mem_nhds isOpen_Ioo hx'
    have hevent : F =ᶠ[nhds x] (fun y => primitive a b y + C) := by
      filter_upwards [hnhds] with y hy
      exact hF y (by simpa [domain] using hy)
    exact hmodel.congr_of_eventuallyEq hevent

end

end ProofGap.Exercise1784
