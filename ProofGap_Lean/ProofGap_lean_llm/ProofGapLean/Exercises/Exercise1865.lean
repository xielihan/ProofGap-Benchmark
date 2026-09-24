import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1865

noncomputable section

def domain : Set ℝ := Set.Ioi 0

def integrand (x : ℝ) : ℝ :=
  (x ^ 2 + 1) / (x * Real.sqrt (x ^ 4 + 1))

def signRewrite (x : ℝ) : ℝ :=
  (1 + 1 / x ^ 2) / Real.sqrt (x ^ 2 + 1 / x ^ 2)

def substitutionRewrite (x : ℝ) : ℝ :=
  (1 + 1 / x ^ 2) / Real.sqrt ((x - 1 / x) ^ 2 + 2)

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

def substitutionPrimitive (x : ℝ) : ℝ :=
  Real.log (x - 1 / x + Real.sqrt ((x - 1 / x) ^ 2 + 2))

def primitive (x : ℝ) : ℝ :=
  Real.log |(x ^ 2 - 1 + Real.sqrt (x ^ 4 + 1)) / x|

private theorem substitution_radicand (x : ℝ) (hx : x ≠ 0) :
    (x - 1 / x) ^ 2 + 2 = x ^ 2 + 1 / x ^ 2 := by
  field_simp [hx]
  <;> ring

private theorem sqrt_scale_on_domain (x : ℝ) (hx : x ∈ domain) :
    Real.sqrt (x ^ 4 + 1) =
      x * Real.sqrt (x ^ 2 + 1 / x ^ 2) := by
  have hxpos : 0 < x := hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hleft : 0 ≤ Real.sqrt (x ^ 4 + 1) := Real.sqrt_nonneg _
  have hrad : 0 ≤ x ^ 2 + 1 / x ^ 2 := by positivity
  have hright : 0 ≤ x * Real.sqrt (x ^ 2 + 1 / x ^ 2) :=
    mul_nonneg hxpos.le (Real.sqrt_nonneg _)
  have hbase : 0 ≤ x ^ 4 + 1 := by positivity
  have hsleft : (Real.sqrt (x ^ 4 + 1)) ^ 2 = x ^ 4 + 1 :=
    Real.sq_sqrt hbase
  have hsright :
      (x * Real.sqrt (x ^ 2 + 1 / x ^ 2)) ^ 2 = x ^ 4 + 1 := by
    rw [mul_pow, Real.sq_sqrt hrad]
    field_simp [hx0]
    <;> ring
  nlinarith

private theorem substitutionPrimitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt substitutionPrimitive (substitutionRewrite x) x := by
  have hxpos : 0 < x := hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  let u : ℝ := x - 1 / x
  let d : ℝ := 1 + 1 / x ^ 2
  let r : ℝ := u ^ 2 + 2
  let q : ℝ := Real.sqrt r
  have hrpos : 0 < r := by
    dsimp [r]
    nlinarith [sq_nonneg u]
  have hqpos : 0 < q := by
    dsimp [q]
    exact Real.sqrt_pos.2 hrpos
  have hq0 : q ≠ 0 := ne_of_gt hqpos
  have hqsq : q ^ 2 = r := by
    dsimp [q]
    exact Real.sq_sqrt hrpos.le
  have hu : HasDerivAt (fun y : ℝ => y - 1 / y) d x := by
    have hraw := (hasDerivAt_id x).sub ((hasDerivAt_id x).inv hx0)
    convert hraw using 1
    · ext y
      simp [one_div]
    · dsimp [d]
      field_simp [hx0]
      <;> ring
  have hr : HasDerivAt
      (fun y : ℝ => (y - 1 / y) ^ 2 + 2) (2 * u * d) x := by
    convert (hu.pow 2).add_const 2 using 1
    <;> dsimp [u]
    <;> ring
  have hqcoef :
      u * d / q = 1 / (2 * q) * (2 * u * d) := by
    field_simp [hq0]
  have hq : HasDerivAt
      (fun y : ℝ => Real.sqrt ((y - 1 / y) ^ 2 + 2)) (u * d / q) x := by
    have hraw := (Real.hasDerivAt_sqrt (ne_of_gt hrpos)).comp x hr
    convert hraw using 1
  have hargpos : 0 < u + q := by
    nlinarith [hqsq]
  have hargcoef :
      d * (u + q) / q = d + u * d / q := by
    field_simp [hq0]
    ring
  have harg : HasDerivAt
      (fun y : ℝ => y - 1 / y +
        Real.sqrt ((y - 1 / y) ^ 2 + 2))
      (d * (u + q) / q) x := by
    convert hu.add hq using 1
  have hlog :=
    (Real.hasDerivAt_log (ne_of_gt hargpos)).comp x harg
  have hlogcoef :
      d / q = (u + q)⁻¹ * (d * (u + q) / q) := by
    field_simp [hq0, ne_of_gt hargpos]
  unfold substitutionPrimitive substitutionRewrite
  convert hlog using 1

private theorem primitive_eq_substitutionPrimitive (x : ℝ) (hx : x ∈ domain) :
    primitive x = substitutionPrimitive x := by
  have hxpos : 0 < x := hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hrad := substitution_radicand x hx0
  have hinnerpos : 0 < (x - 1 / x) ^ 2 + 2 := by
    nlinarith [sq_nonneg (x - 1 / x)]
  have hrootpos :
      0 < Real.sqrt ((x - 1 / x) ^ 2 + 2) :=
    Real.sqrt_pos.2 hinnerpos
  have hrootsq :
      (Real.sqrt ((x - 1 / x) ^ 2 + 2)) ^ 2 =
        (x - 1 / x) ^ 2 + 2 :=
    Real.sq_sqrt hinnerpos.le
  have hargpos :
      0 < x - 1 / x + Real.sqrt ((x - 1 / x) ^ 2 + 2) := by
    nlinarith
  have hfrac :
      (x ^ 2 - 1 + Real.sqrt (x ^ 4 + 1)) / x =
        x - 1 / x + Real.sqrt ((x - 1 / x) ^ 2 + 2) := by
    rw [sqrt_scale_on_domain x hx, hrad]
    field_simp [hx0]
    <;> ring
  unfold primitive substitutionPrimitive
  rw [hfrac, abs_of_pos hargpos]

theorem gap1 : ∀ x ∈ domain, integrand x = signRewrite x := by
  intro x hx
  have hxpos : 0 < x := hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hrpos : 0 < x ^ 2 + 1 / x ^ 2 := by
    have : 0 < x ^ 2 := sq_pos_of_ne_zero hx0
    positivity
  have hr0 : Real.sqrt (x ^ 2 + 1 / x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hrpos)
  unfold integrand signRewrite
  rw [sqrt_scale_on_domain x hx]
  field_simp [hx0, hr0]
  <;> ring

theorem gap2 :
    ∀ x ∈ domain, signRewrite x = substitutionRewrite x := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  unfold signRewrite substitutionRewrite
  rw [substitution_radicand x hx0]

theorem gap3 :
    ∀ x ∈ domain, integrand x = substitutionRewrite x := by
  intro x hx
  calc
    integrand x = signRewrite x := gap1 x hx
    _ = substitutionRewrite x := gap2 x hx

theorem gap4 :
    antiderivatives integrand = antiderivatives signRewrite := by
  ext F
  constructor
  · rintro ⟨hF, hder⟩
    exact ⟨hF, fun x hx => (hder x hx).trans (gap1 x hx)⟩
  · rintro ⟨hF, hder⟩
    exact ⟨hF, fun x hx => (hder x hx).trans (gap1 x hx).symm⟩

theorem gap5 :
    antiderivatives signRewrite = antiderivatives substitutionRewrite := by
  ext F
  constructor
  · rintro ⟨hF, hder⟩
    exact ⟨hF, fun x hx => (hder x hx).trans (gap2 x hx)⟩
  · rintro ⟨hF, hder⟩
    exact ⟨hF, fun x hx => (hder x hx).trans (gap2 x hx).symm⟩

theorem gap6 :
    antiderivatives substitutionRewrite = primitiveFamily substitutionPrimitive := by
  ext F
  constructor
  · rintro ⟨hFdiff, hFder⟩
    let H : ℝ → ℝ := fun t =>
      F (Real.exp t) - substitutionPrimitive (Real.exp t)
    have hH : ∀ t : ℝ, HasDerivAt H 0 t := by
      intro t
      have hzpos : 0 < Real.exp t := Real.exp_pos t
      have hz : Real.exp t ∈ domain := hzpos
      have hnhds : domain ∈ nhds (Real.exp t) :=
        isOpen_Ioi.mem_nhds hzpos
      have hFat : HasDerivAt F (substitutionRewrite (Real.exp t)) (Real.exp t) := by
        have h := (hFdiff (Real.exp t) hz).differentiableAt hnhds
        rw [← hFder (Real.exp t) hz]
        exact h.hasDerivAt
      have hsub : HasDerivAt
          (fun y => F y - substitutionPrimitive y) 0 (Real.exp t) := by
        convert hFat.sub (substitutionPrimitive_hasDerivAt (Real.exp t) hz) using 1
        simp
      change HasDerivAt
        (fun t => F (Real.exp t) - substitutionPrimitive (Real.exp t)) 0 t
      simpa only [Function.comp_apply, zero_mul] using
        hsub.comp t (Real.hasDerivAt_exp t)
    have hHdiff : Differentiable ℝ H :=
      fun t => (hH t).differentiableAt
    have hconst : ∀ t : ℝ, H t = H 0 := by
      intro t
      exact is_const_of_deriv_eq_zero hHdiff (fun z => (hH z).deriv) t 0
    refine ⟨H 0, ?_⟩
    intro x hx
    have hxpos : 0 < x := hx
    have h := hconst (Real.log x)
    dsimp [H] at h ⊢
    rw [Real.exp_log hxpos] at h
    linarith
  · rintro ⟨C, hFC⟩
    have hFat : ∀ x ∈ domain, HasDerivAt F (substitutionRewrite x) x := by
      intro x hx
      have hEq : F =ᶠ[nhds x] fun y => substitutionPrimitive y + C := by
        filter_upwards [show domain ∈ nhds x from isOpen_Ioi.mem_nhds hx] with y hy
        exact hFC y hy
      exact ((substitutionPrimitive_hasDerivAt x hx).add_const C).congr_of_eventuallyEq
        hEq
    constructor
    · intro x hx
      exact (hFat x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hFat x hx).deriv

theorem gap7 :
    antiderivatives integrand = primitiveFamily substitutionPrimitive := by
  calc
    antiderivatives integrand = antiderivatives signRewrite := gap4
    _ = antiderivatives substitutionRewrite := gap5
    _ = primitiveFamily substitutionPrimitive := gap6

theorem gap8 : antiderivatives integrand = primitiveFamily primitive := by
  rw [gap7]
  ext F
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hF x hx, primitive_eq_substitutionPrimitive x hx]
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hF x hx, primitive_eq_substitutionPrimitive x hx]

end

end ProofGap.Exercise1865
