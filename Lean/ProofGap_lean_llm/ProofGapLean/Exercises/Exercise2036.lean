import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2036
noncomputable section

def branch : Set ℝ := Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)
def integrand (x : ℝ) :=
  Real.sin x ^ 2 * Real.cos x ^ 2 / (Real.sin x ^ 8 + Real.cos x ^ 8)
def firstReduced (x : ℝ) :=
  2 * Real.sin (2 * x) ^ 2 /
    (Real.sin (2 * x) ^ 4 - 8 * Real.sin (2 * x) ^ 2 + 8)
def tanReduced (x : ℝ) :=
  Real.tan (2 * x) ^ 2 /
    (Real.tan (2 * x) ^ 4 + 8 * Real.tan (2 * x) ^ 2 + 8) *
      deriv (fun y : ℝ => Real.tan (2 * y)) x
def qplus (u : ℝ) := 1 / (u ^ 2 + 4 + 2 * Real.sqrt 2)
def qminus (u : ℝ) := 1 / (u ^ 2 + 4 - 2 * Real.sqrt 2)
def primitive (x : ℝ) :=
  (1 / 4 : ℝ) *
    (Real.sqrt (2 + Real.sqrt 2) *
        Real.arctan (Real.tan (2 * x) / Real.sqrt (4 + 2 * Real.sqrt 2)) -
      Real.sqrt (2 - Real.sqrt 2) *
        Real.arctan (Real.tan (2 * x) / Real.sqrt (4 - 2 * Real.sqrt 2)))
def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PartialFamily :=
  {F : ℝ → ℝ | ∃ P Q : ℝ → ℝ,
    (∀ x ∈ branch, HasDerivAt P
      (qplus (Real.tan (2 * x)) * deriv (fun y => Real.tan (2 * y)) x) x) ∧
    (∀ x ∈ branch, HasDerivAt Q
      (qminus (Real.tan (2 * x)) * deriv (fun y => Real.tan (2 * y)) x) x) ∧
    (∀ x ∈ branch, F x =
      Real.sqrt 2 / 4 * (2 + Real.sqrt 2) * P x -
      Real.sqrt 2 / 4 * (2 - Real.sqrt 2) * Q x)}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ branch, F x = p x + C}

theorem gap1 (x : ℝ) : integrand x = firstReduced x := by
  unfold integrand firstReduced
  have hsc := Real.sin_sq_add_cos_sq x
  have hden :
      Real.sin (2 * x) ^ 4 - 8 * Real.sin (2 * x) ^ 2 + 8 =
        8 * (Real.sin x ^ 8 + Real.cos x ^ 8) := by
    rw [Real.sin_two_mul]
    linear_combination
      (-8 * ((Real.sin x ^ 2 + Real.cos x ^ 2) ^ 3 +
          (Real.sin x ^ 2 + Real.cos x ^ 2) ^ 2 +
          (Real.sin x ^ 2 + Real.cos x ^ 2) + 1) +
        32 * Real.sin x ^ 2 * Real.cos x ^ 2 *
          (Real.sin x ^ 2 + Real.cos x ^ 2 + 1)) * hsc
  have hs_or_hc : Real.sin x ≠ 0 ∨ Real.cos x ≠ 0 := by
    by_contra h
    simp only [not_or, not_ne_iff] at h
    rw [h.1, h.2] at hsc
    norm_num at hsc
  have hpos : 0 < Real.sin x ^ 8 + Real.cos x ^ 8 := by
    rcases hs_or_hc with hs | hc
    · have hs4 : Real.sin x ^ 4 ≠ 0 := pow_ne_zero 4 hs
      have hs8 : 0 < Real.sin x ^ 8 := by
        calc
          Real.sin x ^ 8 = (Real.sin x ^ 4) ^ 2 := by ring
          _ > 0 := sq_pos_of_ne_zero hs4
      exact add_pos_of_pos_of_nonneg hs8 (by positivity)
    · have hc4 : Real.cos x ^ 4 ≠ 0 := pow_ne_zero 4 hc
      have hc8 : 0 < Real.cos x ^ 8 := by
        calc
          Real.cos x ^ 8 = (Real.cos x ^ 4) ^ 2 := by ring
          _ > 0 := sq_pos_of_ne_zero hc4
      exact add_pos_of_nonneg_of_pos (by positivity) hc8
  rw [hden, Real.sin_two_mul]
  field_simp [ne_of_gt hpos] <;> ring
theorem gap2 (x : ℝ) (hx : x ∈ branch) : integrand x = tanReduced x := by
  rw [gap1]
  unfold firstReduced tanReduced
  have hx' : -(Real.pi / 2) < 2 * x ∧ 2 * x < Real.pi / 2 := by
    unfold branch at hx
    constructor <;> nlinarith [hx.1, hx.2]
  have hcospos : 0 < Real.cos (2 * x) := Real.cos_pos_of_mem_Ioo hx'
  have hcos : Real.cos (2 * x) ≠ 0 := ne_of_gt hcospos
  let t : ℝ → ℝ := fun y => Real.tan (2 * y)
  have ht0 : HasDerivAt t (2 / Real.cos (2 * x) ^ 2) x := by
    convert (Real.hasDerivAt_tan hcos).comp x ((hasDerivAt_id x).const_mul 2) using 1 <;> ring
  have hdt : deriv t x = 2 / Real.cos (2 * x) ^ 2 := ht0.deriv
  have hsc := Real.sin_sq_add_cos_sq (2 * x)
  have hden :
      Real.sin (2 * x) ^ 4 - 8 * Real.sin (2 * x) ^ 2 + 8 =
        Real.sin (2 * x) ^ 4 +
          8 * Real.sin (2 * x) ^ 2 * Real.cos (2 * x) ^ 2 +
          8 * Real.cos (2 * x) ^ 4 := by
    calc
      Real.sin (2 * x) ^ 4 - 8 * Real.sin (2 * x) ^ 2 + 8 =
          Real.sin (2 * x) ^ 4 + 8 * Real.cos (2 * x) ^ 2 := by
            nlinarith [hsc]
      _ = Real.sin (2 * x) ^ 4 +
          8 * Real.sin (2 * x) ^ 2 * Real.cos (2 * x) ^ 2 +
          8 * Real.cos (2 * x) ^ 4 := by
            linear_combination
              (-8 * Real.cos (2 * x) ^ 2) * hsc
  have hleft :
      0 < Real.sin (2 * x) ^ 4 +
          8 * Real.sin (2 * x) ^ 2 * Real.cos (2 * x) ^ 2 +
          8 * Real.cos (2 * x) ^ 4 := by
    have hc2 : 0 < Real.cos (2 * x) ^ 2 := sq_pos_of_ne_zero hcos
    nlinarith [sq_nonneg (Real.sin (2 * x) ^ 2),
      sq_nonneg (Real.cos (2 * x) ^ 2)]
  rw [hden, show deriv (fun y : ℝ => Real.tan (2 * y)) x =
      2 / Real.cos (2 * x) ^ 2 by exact hdt]
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcos, ne_of_gt hleft] <;> ring
theorem gap3 : Family integrand = PartialFamily := by
  let A : ℝ := Real.sqrt 2 / 4 * (2 + Real.sqrt 2)
  let B : ℝ := Real.sqrt 2 / 4 * (2 - Real.sqrt 2)
  let P₀ : ℝ → ℝ := fun x =>
    1 / Real.sqrt (4 + 2 * Real.sqrt 2) *
      Real.arctan (Real.tan (2 * x) / Real.sqrt (4 + 2 * Real.sqrt 2))
  let Q₀ : ℝ → ℝ := fun x =>
    1 / Real.sqrt (4 - 2 * Real.sqrt 2) *
      Real.arctan (Real.tan (2 * x) / Real.sqrt (4 - 2 * Real.sqrt 2))
  have hr2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hr0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hm : 0 < 4 - 2 * Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hp : 0 < 4 + 2 * Real.sqrt 2 := by positivity
  have hA : A ≠ 0 := by
    dsimp [A]
    positivity
  have haux : ∀ (a : ℝ), 0 < a → ∀ x ∈ branch,
      HasDerivAt
        (fun y => 1 / Real.sqrt a *
          Real.arctan (Real.tan (2 * y) / Real.sqrt a))
        (1 / (Real.tan (2 * x) ^ 2 + a) *
          deriv (fun y => Real.tan (2 * y)) x) x := by
    intro a ha x hx
    have hx' : -(Real.pi / 2) < 2 * x ∧ 2 * x < Real.pi / 2 := by
      unfold branch at hx
      constructor <;> nlinarith [hx.1, hx.2]
    have hc : Real.cos (2 * x) ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo hx')
    let t : ℝ → ℝ := fun y => Real.tan (2 * y)
    have ht0 : HasDerivAt t (2 / Real.cos (2 * x) ^ 2) x := by
      convert (Real.hasDerivAt_tan hc).comp x ((hasDerivAt_id x).const_mul 2) using 1 <;> ring
    have ht : HasDerivAt t (deriv t x) x := ht0.differentiableAt.hasDerivAt
    have hs : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ha)
    have hs2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
    have hqa : 0 < Real.tan (2 * x) ^ 2 + a := by
      nlinarith [sq_nonneg (Real.tan (2 * x))]
    have hqb : 0 < 1 + (Real.tan (2 * x) / Real.sqrt a) ^ 2 := by
      positivity
    have hfrac :
        1 / (Real.tan (2 * x) ^ 2 + a) =
          1 / Real.sqrt a *
            (1 / (1 + (Real.tan (2 * x) / Real.sqrt a) ^ 2) *
              (1 / Real.sqrt a)) := by
      field_simp [hs, ne_of_gt hqa, ne_of_gt hqb] <;> nlinarith [hs2]
    have harctan :=
      ((Real.hasDerivAt_arctan (t x / Real.sqrt a)).comp x
        (ht.div_const (Real.sqrt a))).const_mul (1 / Real.sqrt a)
    convert harctan using 1
    dsimp [t]
    rw [hfrac]
    ring
  have hP : ∀ x ∈ branch, HasDerivAt P₀
      (qplus (Real.tan (2 * x)) * deriv (fun y => Real.tan (2 * y)) x) x := by
    intro x hx
    simpa [P₀, qplus, add_assoc] using haux (4 + 2 * Real.sqrt 2) hp x hx
  have hQ : ∀ x ∈ branch, HasDerivAt Q₀
      (qminus (Real.tan (2 * x)) * deriv (fun y => Real.tan (2 * y)) x) x := by
    intro x hx
    simpa [Q₀, qminus, sub_eq_add_neg, add_assoc] using
      haux (4 - 2 * Real.sqrt 2) hm x hx
  have hpartial : ∀ x ∈ branch,
      integrand x =
        A * (qplus (Real.tan (2 * x)) * deriv (fun y => Real.tan (2 * y)) x) -
        B * (qminus (Real.tan (2 * x)) * deriv (fun y => Real.tan (2 * y)) x) := by
    intro x hx
    rw [gap2 x hx]
    unfold tanReduced qplus qminus
    have h₁ : 0 < Real.tan (2 * x) ^ 2 + 4 + 2 * Real.sqrt 2 := by
      positivity
    have h₂ : 0 < Real.tan (2 * x) ^ 2 + 4 - 2 * Real.sqrt 2 := by
      nlinarith [sq_nonneg (Real.tan (2 * x))]
    have hfac :
        Real.tan (2 * x) ^ 4 + 8 * Real.tan (2 * x) ^ 2 + 8 =
          (Real.tan (2 * x) ^ 2 + 4 + 2 * Real.sqrt 2) *
            (Real.tan (2 * x) ^ 2 + 4 - 2 * Real.sqrt 2) := by
      nlinarith [hr2]
    have hAB : A - B = 1 := by
      dsimp [A, B]
      nlinarith [hr2]
    have hconstant :
        A * (4 - 2 * Real.sqrt 2) -
          B * (4 + 2 * Real.sqrt 2) = 0 := by
      dsimp [A, B]
      ring
    have hnum :
        A * (Real.tan (2 * x) ^ 2 + 4 - 2 * Real.sqrt 2) -
          B * (Real.tan (2 * x) ^ 2 + 4 + 2 * Real.sqrt 2) =
            Real.tan (2 * x) ^ 2 := by
      calc
        A * (Real.tan (2 * x) ^ 2 + 4 - 2 * Real.sqrt 2) -
            B * (Real.tan (2 * x) ^ 2 + 4 + 2 * Real.sqrt 2) =
          (A - B) * Real.tan (2 * x) ^ 2 +
            (A * (4 - 2 * Real.sqrt 2) -
              B * (4 + 2 * Real.sqrt 2)) := by ring
        _ = Real.tan (2 * x) ^ 2 := by rw [hAB, hconstant]; ring
    have hrat :
        Real.tan (2 * x) ^ 2 /
            (Real.tan (2 * x) ^ 4 + 8 * Real.tan (2 * x) ^ 2 + 8) =
          A / (Real.tan (2 * x) ^ 2 + 4 + 2 * Real.sqrt 2) -
            B / (Real.tan (2 * x) ^ 2 + 4 - 2 * Real.sqrt 2) := by
      rw [hfac]
      field_simp [ne_of_gt h₁, ne_of_gt h₂] <;> nlinarith [hnum]
    rw [hrat]
    ring
  apply Set.ext
  intro F
  constructor
  · intro hF
    have hG : ∀ x ∈ branch,
        HasDerivAt (fun y => A * P₀ y - B * Q₀ y) (integrand x) x := by
      intro x hx
      have h := (hP x hx).const_mul A |>.sub ((hQ x hx).const_mul B)
      convert h using 1
      simpa [hpartial x hx]
    let G : ℝ → ℝ := fun y => A * P₀ y - B * Q₀ y
    let H : ℝ → ℝ := fun y => F y - G y
    have hdiff : DifferentiableOn ℝ H branch := by
      intro x hx
      exact ((hF x hx).sub (hG x hx)).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ branch, deriv H x = 0 := by
      intro x hx
      change deriv (fun y => F y - (A * P₀ y - B * Q₀ y)) x = 0
      simpa using ((hF x hx).sub (hG x hx)).deriv
    have hzero_mem : (0 : ℝ) ∈ branch := by
      unfold branch
      constructor <;> nlinarith [Real.pi_pos]
    let C : ℝ := H 0
    have hconst : ∀ x ∈ branch, H x = C := by
      intro x hx
      exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hdiff hzero hx hzero_mem
    refine ⟨fun y => P₀ y + C / A, Q₀, ?_, hQ, ?_⟩
    · intro x hx
      simpa using (hP x hx).add_const (C / A)
    · intro x hx
      have hc := hconst x hx
      change F x - (A * P₀ x - B * Q₀ x) = C at hc
      change F x = A * (P₀ x + C / A) - B * Q₀ x
      have hc' : F x = A * P₀ x - B * Q₀ x + C := by linarith
      rw [hc']
      field_simp [hA] <;> ring
  · intro hF
    rcases hF with ⟨P, Q, hP', hQ', hrel⟩
    intro x hx
    have hlin := (hP' x hx).const_mul A |>.sub ((hQ' x hx).const_mul B)
    have hev : F =ᶠ[nhds x] (fun y => A * P y) - fun y => B * Q y := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      change F y = A * P y - B * Q y
      simpa [A, B] using hrel y hy
    have hd := hlin.congr_of_eventuallyEq hev
    convert hd using 1
    simpa [hpartial x hx]
theorem gap4 : Family integrand = Translates primitive := by
  let A : ℝ := Real.sqrt 2 / 4 * (2 + Real.sqrt 2)
  let B : ℝ := Real.sqrt 2 / 4 * (2 - Real.sqrt 2)
  let P₀ : ℝ → ℝ := fun x =>
    1 / Real.sqrt (4 + 2 * Real.sqrt 2) *
      Real.arctan (Real.tan (2 * x) / Real.sqrt (4 + 2 * Real.sqrt 2))
  let Q₀ : ℝ → ℝ := fun x =>
    1 / Real.sqrt (4 - 2 * Real.sqrt 2) *
      Real.arctan (Real.tan (2 * x) / Real.sqrt (4 - 2 * Real.sqrt 2))
  have hr2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hr0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsp : 0 < 2 + Real.sqrt 2 := by positivity
  have hsm : 0 < 2 - Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hp : 0 < 4 + 2 * Real.sqrt 2 := by positivity
  have hm : 0 < 4 - 2 * Real.sqrt 2 := by nlinarith
  have hsplus :
      Real.sqrt (4 + 2 * Real.sqrt 2) =
        Real.sqrt 2 * Real.sqrt (2 + Real.sqrt 2) := by
    have h1 := Real.sq_sqrt hp.le
    have h2 := Real.sq_sqrt hsp.le
    have hn1 := Real.sqrt_nonneg (4 + 2 * Real.sqrt 2)
    have hn2 := Real.sqrt_nonneg (2 + Real.sqrt 2)
    have hprod :
        (Real.sqrt 2 * Real.sqrt (2 + Real.sqrt 2)) ^ 2 =
          4 + 2 * Real.sqrt 2 := by
      rw [mul_pow, hr2, h2]
      ring
    have hnprod : 0 ≤ Real.sqrt 2 * Real.sqrt (2 + Real.sqrt 2) :=
      mul_nonneg (Real.sqrt_nonneg 2) hn2
    nlinarith
  have hsminus :
      Real.sqrt (4 - 2 * Real.sqrt 2) =
        Real.sqrt 2 * Real.sqrt (2 - Real.sqrt 2) := by
    have h1 := Real.sq_sqrt hm.le
    have h2 := Real.sq_sqrt hsm.le
    have hn1 := Real.sqrt_nonneg (4 - 2 * Real.sqrt 2)
    have hn2 := Real.sqrt_nonneg (2 - Real.sqrt 2)
    have hprod :
        (Real.sqrt 2 * Real.sqrt (2 - Real.sqrt 2)) ^ 2 =
          4 - 2 * Real.sqrt 2 := by
      rw [mul_pow, hr2, h2]
      ring
    have hnprod : 0 ≤ Real.sqrt 2 * Real.sqrt (2 - Real.sqrt 2) :=
      mul_nonneg (Real.sqrt_nonneg 2) hn2
    nlinarith
  have haux : ∀ (a : ℝ), 0 < a → ∀ x ∈ branch,
      HasDerivAt
        (fun y => 1 / Real.sqrt a *
          Real.arctan (Real.tan (2 * y) / Real.sqrt a))
        (1 / (Real.tan (2 * x) ^ 2 + a) *
          deriv (fun y => Real.tan (2 * y)) x) x := by
    intro a ha x hx
    have hx' : -(Real.pi / 2) < 2 * x ∧ 2 * x < Real.pi / 2 := by
      unfold branch at hx
      constructor <;> nlinarith [hx.1, hx.2]
    have hc : Real.cos (2 * x) ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo hx')
    let t : ℝ → ℝ := fun y => Real.tan (2 * y)
    have ht0 : HasDerivAt t (2 / Real.cos (2 * x) ^ 2) x := by
      convert (Real.hasDerivAt_tan hc).comp x ((hasDerivAt_id x).const_mul 2) using 1 <;> ring
    have ht : HasDerivAt t (deriv t x) x := ht0.differentiableAt.hasDerivAt
    have hs : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ha)
    have hs2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
    have hqa : 0 < Real.tan (2 * x) ^ 2 + a := by
      nlinarith [sq_nonneg (Real.tan (2 * x))]
    have hqb : 0 < 1 + (Real.tan (2 * x) / Real.sqrt a) ^ 2 := by
      positivity
    have hfrac :
        1 / (Real.tan (2 * x) ^ 2 + a) =
          1 / Real.sqrt a *
            (1 / (1 + (Real.tan (2 * x) / Real.sqrt a) ^ 2) *
              (1 / Real.sqrt a)) := by
      field_simp [hs, ne_of_gt hqa, ne_of_gt hqb] <;> nlinarith [hs2]
    have harctan :=
      ((Real.hasDerivAt_arctan (t x / Real.sqrt a)).comp x
        (ht.div_const (Real.sqrt a))).const_mul (1 / Real.sqrt a)
    convert harctan using 1
    dsimp [t]
    rw [hfrac]
    ring
  have hP : ∀ x ∈ branch, HasDerivAt P₀
      (qplus (Real.tan (2 * x)) * deriv (fun y => Real.tan (2 * y)) x) x := by
    intro x hx
    simpa [P₀, qplus, add_assoc] using haux (4 + 2 * Real.sqrt 2) hp x hx
  have hQ : ∀ x ∈ branch, HasDerivAt Q₀
      (qminus (Real.tan (2 * x)) * deriv (fun y => Real.tan (2 * y)) x) x := by
    intro x hx
    simpa [Q₀, qminus, sub_eq_add_neg, add_assoc] using
      haux (4 - 2 * Real.sqrt 2) hm x hx
  have hneR : Real.sqrt 2 ≠ 0 := ne_of_gt hr0
  have hneP : Real.sqrt (2 + Real.sqrt 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hsp)
  have hneM : Real.sqrt (2 - Real.sqrt 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hsm)
  have hsP2 : Real.sqrt (2 + Real.sqrt 2) ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt hsp.le
  have hsM2 : Real.sqrt (2 - Real.sqrt 2) ^ 2 = 2 - Real.sqrt 2 :=
    Real.sq_sqrt hsm.le
  have hcoefplus :
      A * (1 / Real.sqrt (4 + 2 * Real.sqrt 2)) =
        (1 / 4 : ℝ) * Real.sqrt (2 + Real.sqrt 2) := by
    calc
      A * (1 / Real.sqrt (4 + 2 * Real.sqrt 2)) =
          (Real.sqrt 2 / 4 * (2 + Real.sqrt 2)) /
            (Real.sqrt 2 * Real.sqrt (2 + Real.sqrt 2)) := by
              rw [hsplus]
              dsimp [A]
              ring
      _ = (2 + Real.sqrt 2) /
          (4 * Real.sqrt (2 + Real.sqrt 2)) := by
            field_simp [hneR, hneP] <;> ring
      _ = (1 / 4 : ℝ) * Real.sqrt (2 + Real.sqrt 2) := by
            field_simp [hneP] <;> nlinarith [hsP2]
  have hcoefminus :
      B * (1 / Real.sqrt (4 - 2 * Real.sqrt 2)) =
        (1 / 4 : ℝ) * Real.sqrt (2 - Real.sqrt 2) := by
    calc
      B * (1 / Real.sqrt (4 - 2 * Real.sqrt 2)) =
          (Real.sqrt 2 / 4 * (2 - Real.sqrt 2)) /
            (Real.sqrt 2 * Real.sqrt (2 - Real.sqrt 2)) := by
              rw [hsminus]
              dsimp [B]
              ring
      _ = (2 - Real.sqrt 2) /
          (4 * Real.sqrt (2 - Real.sqrt 2)) := by
            field_simp [hneR, hneM] <;> ring
      _ = (1 / 4 : ℝ) * Real.sqrt (2 - Real.sqrt 2) := by
            field_simp [hneM] <;> nlinarith [hsM2]
  have hprimitive : ∀ x,
      primitive x = A * P₀ x - B * Q₀ x := by
    intro x
    unfold primitive
    dsimp only [P₀, Q₀]
    calc
      (1 / 4 : ℝ) *
          (Real.sqrt (2 + Real.sqrt 2) *
              Real.arctan (Real.tan (2 * x) / Real.sqrt (4 + 2 * Real.sqrt 2)) -
            Real.sqrt (2 - Real.sqrt 2) *
              Real.arctan (Real.tan (2 * x) / Real.sqrt (4 - 2 * Real.sqrt 2))) =
        ((1 / 4 : ℝ) * Real.sqrt (2 + Real.sqrt 2)) *
              Real.arctan (Real.tan (2 * x) / Real.sqrt (4 + 2 * Real.sqrt 2)) -
          ((1 / 4 : ℝ) * Real.sqrt (2 - Real.sqrt 2)) *
              Real.arctan (Real.tan (2 * x) / Real.sqrt (4 - 2 * Real.sqrt 2)) := by
                ring
      _ = (A * (1 / Real.sqrt (4 + 2 * Real.sqrt 2))) *
              Real.arctan (Real.tan (2 * x) / Real.sqrt (4 + 2 * Real.sqrt 2)) -
          (B * (1 / Real.sqrt (4 - 2 * Real.sqrt 2))) *
              Real.arctan (Real.tan (2 * x) / Real.sqrt (4 - 2 * Real.sqrt 2)) := by
                rw [hcoefplus, hcoefminus]
      _ = A *
              (1 / Real.sqrt (4 + 2 * Real.sqrt 2) *
                Real.arctan (Real.tan (2 * x) / Real.sqrt (4 + 2 * Real.sqrt 2))) -
          B *
              (1 / Real.sqrt (4 - 2 * Real.sqrt 2) *
                Real.arctan (Real.tan (2 * x) / Real.sqrt (4 - 2 * Real.sqrt 2))) := by
                ring
  have hcanonical : (fun z => A * P₀ z - B * Q₀ z) ∈ PartialFamily := by
    refine ⟨P₀, Q₀, hP, hQ, ?_⟩
    intro x hx
    rfl
  have hcanFamily : (fun z => A * P₀ z - B * Q₀ z) ∈ Family integrand := by
    rw [gap3]
    exact hcanonical
  have hfun : primitive = fun z => A * P₀ z - B * Q₀ z := by
    funext x
    exact hprimitive x
  have hprim_deriv : ∀ x ∈ branch, HasDerivAt primitive (integrand x) x := by
    intro x hx
    rw [hfun]
    exact hcanFamily x hx
  apply Set.ext
  intro F
  constructor
  · intro hF
    let H : ℝ → ℝ := fun x => F x - primitive x
    have hdiff : DifferentiableOn ℝ H branch := by
      intro x hx
      exact ((hF x hx).sub (hprim_deriv x hx)).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ branch, deriv H x = 0 := by
      intro x hx
      change deriv (fun y => F y - primitive y) x = 0
      simpa using ((hF x hx).sub (hprim_deriv x hx)).deriv
    have hzero_mem : (0 : ℝ) ∈ branch := by
      unfold branch
      constructor <;> nlinarith [Real.pi_pos]
    refine ⟨H 0, ?_⟩
    intro x hx
    have hc := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      hdiff hzero hx hzero_mem
    dsimp [H] at hc ⊢
    linarith
  · rintro ⟨C, hC⟩ x hx
    have hev : F =ᶠ[nhds x] fun y => primitive y + C := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hC y hy
    have hd := (hprim_deriv x hx).add_const C
    exact hd.congr_of_eventuallyEq hev

end
end ProofGap.Exercise2036
