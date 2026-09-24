import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1662

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / (2 - 3 * x ^ 2)
def intermediate (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.sqrt (2 / 3) * (1 / 2) *
    Real.log |(1 + Real.sqrt (3 / 2) * x) /
      (1 - Real.sqrt (3 / 2) * x)|
def primitive (x : ℝ) : ℝ :=
  1 / (2 * Real.sqrt 6) *
    Real.log |(Real.sqrt 2 + x * Real.sqrt 3) /
      (Real.sqrt 2 - x * Real.sqrt 3)|
def domain : Set ℝ := {x | 2 - 3 * x ^ 2 ≠ 0}

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem intermediate_eq_primitive_all : intermediate = primitive := by
  funext x
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have hs6 : Real.sqrt 6 ≠ 0 := by positivity
  have hmul :
      Real.sqrt 2 * Real.sqrt (3 / 2) = Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hratio :
      (1 + Real.sqrt (3 / 2) * x) /
          (1 - Real.sqrt (3 / 2) * x) =
        (Real.sqrt 2 + x * Real.sqrt 3) /
          (Real.sqrt 2 - x * Real.sqrt 3) := by
    symm
    calc
      (Real.sqrt 2 + x * Real.sqrt 3) /
          (Real.sqrt 2 - x * Real.sqrt 3) =
          (Real.sqrt 2 * (1 + Real.sqrt (3 / 2) * x)) /
            (Real.sqrt 2 * (1 - Real.sqrt (3 / 2) * x)) := by
              rw [← hmul]
              congr 1 <;> ring
      _ = (1 + Real.sqrt (3 / 2) * x) /
          (1 - Real.sqrt (3 / 2) * x) := by
            exact mul_div_mul_left _ _ hs2
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    have hs0 : 0 ≤ Real.sqrt (4 : ℝ) := Real.sqrt_nonneg _
    have hs4 : (Real.sqrt (4 : ℝ)) ^ 2 = 4 :=
      Real.sq_sqrt (by norm_num)
    nlinarith
  have hprod : Real.sqrt (2 / 3) * Real.sqrt 6 = 2 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    convert hsqrt4 using 1 <;> norm_num
  have hcoef :
      (1 / 2 : ℝ) * Real.sqrt (2 / 3) * (1 / 2) =
        1 / (2 * Real.sqrt 6) := by
    calc
      (1 / 2 : ℝ) * Real.sqrt (2 / 3) * (1 / 2) =
          Real.sqrt (2 / 3) / 4 := by ring
      _ = 1 / (2 * Real.sqrt 6) := by
        field_simp [hs6]
        nlinarith [hprod]
  unfold intermediate primitive
  rw [hratio, hcoef]

theorem gap1 (x : ℝ) :
    integrand x = (1 / 2 : ℝ) /
      (1 - (Real.sqrt (3 / 2) * x) ^ 2) := by
  have hs : (Real.sqrt (3 / 2)) ^ 2 = (3 / 2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  unfold integrand
  rw [mul_pow, hs]
  have hden :
      1 - (3 / 2 : ℝ) * x ^ 2 =
        (1 / 2 : ℝ) * (2 - 3 * x ^ 2) := by
    ring
  rw [hden]
  simp [div_eq_mul_inv, mul_comm]

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt intermediate (integrand x) x := by
  change 2 - 3 * x ^ 2 ≠ 0 at hx
  let a : ℝ := Real.sqrt (3 / 2)
  have ha_sq : a ^ 2 = (3 / 2 : ℝ) := by
    dsimp [a]
    exact Real.sq_sqrt (by norm_num)
  have hdomain_factor :
      2 - 3 * x ^ 2 = 2 * (1 - (a * x) ^ 2) := by
    rw [mul_pow, ha_sq]
    ring
  have hden : 1 - a * x ≠ 0 := by
    intro h
    apply hx
    rw [hdomain_factor]
    have hz : 1 - (a * x) ^ 2 = 0 := by
      calc
        1 - (a * x) ^ 2 = (1 - a * x) * (1 + a * x) := by ring
        _ = 0 := by rw [h]; ring
    rw [hz]
    ring
  have hnum : 1 + a * x ≠ 0 := by
    intro h
    apply hx
    rw [hdomain_factor]
    have hz : 1 - (a * x) ^ 2 = 0 := by
      calc
        1 - (a * x) ^ 2 = (1 - a * x) * (1 + a * x) := by ring
        _ = 0 := by rw [h]; ring
    rw [hz]
    ring
  have hquad : 1 - (a * x) ^ 2 ≠ 0 := by
    rw [show 1 - (a * x) ^ 2 = (1 - a * x) * (1 + a * x) by ring]
    exact mul_ne_zero hden hnum
  have hu : HasDerivAt (fun y : ℝ => 1 + a * y) a x := by
    convert (hasDerivAt_const x (1 : ℝ)).add
      ((hasDerivAt_id x).const_mul a) using 1 <;> ring
  have hv : HasDerivAt (fun y : ℝ => 1 - a * y) (-a) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub
      ((hasDerivAt_id x).const_mul a) using 1 <;> ring
  have hquot :
      HasDerivAt (fun y : ℝ => (1 + a * y) / (1 - a * y))
        (2 * a / (1 - a * x) ^ 2) x := by
    convert hu.div hv hden using 1 <;> ring
  have hqne : (1 + a * x) / (1 - a * x) ≠ 0 :=
    div_ne_zero hnum hden
  have hlograw :
      HasDerivAt
        (fun y : ℝ => Real.log ((1 + a * y) / (1 - a * y)))
        ((2 * a / (1 - a * x) ^ 2) /
          ((1 + a * x) / (1 - a * x))) x := by
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_comm] using
      ((Real.hasDerivAt_log hqne).comp x hquot)
  have hlog_deriv :
      (2 * a / (1 - a * x) ^ 2) /
          ((1 + a * x) / (1 - a * x)) =
        2 * a / (1 - (a * x) ^ 2) := by
    have hfactor :
        1 - (a * x) ^ 2 = (1 - a * x) * (1 + a * x) := by
      ring
    rw [hfactor]
    field_simp [hden, hnum] <;> ring
  have hlog :
      HasDerivAt
        (fun y : ℝ => Real.log ((1 + a * y) / (1 - a * y)))
        (2 * a / (1 - (a * x) ^ 2)) x := by
    rw [hlog_deriv] at hlograw
    exact hlograw
  have haprod : Real.sqrt (2 / 3) * a = 1 := by
    dsimp [a]
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    norm_num
  let k : ℝ := (1 / 2 : ℝ) * Real.sqrt (2 / 3) * (1 / 2)
  have hcoef :
      k * (2 * a / (1 - (a * x) ^ 2)) =
        (1 / 2 : ℝ) / (1 - (a * x) ^ 2) := by
    dsimp [k]
    calc
      (1 / 2 : ℝ) * Real.sqrt (2 / 3) * (1 / 2) *
          (2 * a / (1 - (a * x) ^ 2)) =
          (Real.sqrt (2 / 3) * a / 2) /
            (1 - (a * x) ^ 2) := by ring
      _ = (1 / 2 : ℝ) / (1 - (a * x) ^ 2) := by
        rw [haprod]
  rw [gap1 x, ← hcoef]
  change HasDerivAt
    (fun y : ℝ => k * Real.log |(1 + a * y) / (1 - a * y)|)
    (k * (2 * a / (1 - (a * x) ^ 2))) x
  simpa only [Real.log_abs] using hlog.const_mul k

theorem gap3 (x : ℝ) (hx : x ∈ domain) :
    intermediate x = primitive x := by
  exact congrFun intermediate_eq_primitive_all x

theorem gap4 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  have hprimitive :
      ∀ x ∈ s, HasDerivAt primitive (integrand x) x := by
    intro x hx
    rw [← intermediate_eq_primitive_all]
    exact gap2 x (hdom hx)
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand s at hF
    change ∃ C, ∀ x ∈ s, F x = primitive x + C
    have hzero :
        ∀ x ∈ s, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (hprimitive x hx)
    have hdiff :
        DifferentiableOn ℝ (fun y => F y - primitive y) s := by
      intro y hy
      exact (hzero y hy).differentiableAt.differentiableWithinAt
    have hderiv :
        ∀ y ∈ s, deriv (fun z => F z - primitive z) y = 0 := by
      intro y hy
      exact (hzero y hy).deriv
    by_cases hne : s.Nonempty
    · obtain ⟨x₀, hx₀⟩ := hne
      refine ⟨F x₀ - primitive x₀, ?_⟩
      intro x hx
      have hc :
          F x - primitive x = F x₀ - primitive x₀ :=
        hopen.is_const_of_deriv_eq_zero hs hdiff hderiv hx hx₀
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hne ⟨x, hx⟩).elim
  · intro hF
    change ∃ C, ∀ x ∈ s, F x = primitive x + C at hF
    change IsAntiderivativeOn F integrand s
    obtain ⟨C, hC⟩ := hF
    intro x hx
    have heq : F =ᶠ[nhds x] fun y => primitive y + C := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact ((hprimitive x hx).add_const C).congr_of_eventuallyEq heq

end

end ProofGap.Exercise1662
