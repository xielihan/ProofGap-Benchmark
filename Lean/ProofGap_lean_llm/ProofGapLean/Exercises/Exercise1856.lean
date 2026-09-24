import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1856

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / (x * Real.sqrt (x ^ 2 + x + 1))

def antiderivativesOn (s : Set ℝ) (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F s ∧ ∀ x ∈ s, deriv F x = g x}

def primitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}

def positiveDomain : Set ℝ := Set.Ioi 0

def negativeDomain : Set ℝ := Set.Iio 0

def positiveSubstitutionPrimitive (x : ℝ) : ℝ :=
  -Real.log |1 / x + 1 / 2 +
    Real.sqrt ((1 / x) ^ 2 + 1 / x + 1)|

def positivePrimitive (x : ℝ) : ℝ :=
  -Real.log |(x + 2 + 2 * Real.sqrt (x ^ 2 + x + 1)) / x|

def negativeSubstitutionPrimitive (x : ℝ) : ℝ :=
  -Real.log |-1 / x - 1 / 2 +
    Real.sqrt ((-1 / x) ^ 2 - (-1 / x) + 1)|

def negativePrimitive (x : ℝ) : ℝ :=
  -Real.log |(-x - 2 - 2 * Real.sqrt (x ^ 2 + x + 1)) / x|

private theorem sqrt_mul_eq_sqrt_of_mul_sq_eq
    (a b u : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u)
    (h : a * u ^ 2 = b) :
    Real.sqrt a * u = Real.sqrt b := by
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have hsq : (Real.sqrt a * u) ^ 2 = Real.sqrt b ^ 2 := by
    rw [mul_pow, hsa, hsb]
    exact h
  have hlu : 0 ≤ Real.sqrt a * u :=
    mul_nonneg (Real.sqrt_nonneg a) hu
  nlinarith [Real.sqrt_nonneg b]

private def logSqrtPrimitive (z : ℝ) : ℝ :=
  -Real.log |z + Real.sqrt (z ^ 2 + 3 / 4)|

private theorem hasDerivAt_logSqrtPrimitive (z : ℝ) :
    HasDerivAt logSqrtPrimitive (-1 / Real.sqrt (z ^ 2 + 3 / 4)) z := by
  have hq : 0 < z ^ 2 + 3 / 4 := by nlinarith [sq_nonneg z]
  have hr0 : Real.sqrt (z ^ 2 + 3 / 4) ≠ 0 :=
    (Real.sqrt_pos.2 hq).ne'
  have hinside :
      HasDerivAt (fun y : ℝ => y ^ 2 + 3 / 4) (2 * z) z := by
    convert ((hasDerivAt_id z).pow 2).add_const (3 / 4) using 1 <;>
      simp only [id_eq] <;> ring
  have hsqrt :
      HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 + 3 / 4))
        (z / Real.sqrt (z ^ 2 + 3 / 4)) z := by
    convert (Real.hasDerivAt_sqrt hq.ne').comp z hinside using 1 <;>
      field_simp [hr0] <;> ring
  have hsum :
      HasDerivAt (fun y : ℝ => y + Real.sqrt (y ^ 2 + 3 / 4))
        (1 + z / Real.sqrt (z ^ 2 + 3 / 4)) z :=
    (hasDerivAt_id z).add hsqrt
  have hsum' :
      HasDerivAt (fun y : ℝ => y + Real.sqrt (y ^ 2 + 3 / 4))
        ((z + Real.sqrt (z ^ 2 + 3 / 4)) /
          Real.sqrt (z ^ 2 + 3 / 4)) z := by
    convert hsum using 1 <;> field_simp [hr0] <;> ring
  have hpos : 0 < z + Real.sqrt (z ^ 2 + 3 / 4) := by
    have hsquare : Real.sqrt (z ^ 2 + 3 / 4) ^ 2 = z ^ 2 + 3 / 4 :=
      Real.sq_sqrt hq.le
    nlinarith [Real.sqrt_nonneg (z ^ 2 + 3 / 4)]
  have habs :
      (fun y : ℝ => -Real.log |y + Real.sqrt (y ^ 2 + 3 / 4)|) =
        (fun y : ℝ => -Real.log (y + Real.sqrt (y ^ 2 + 3 / 4))) := by
    funext y
    have hyq : 0 < y ^ 2 + 3 / 4 := by
      nlinarith [sq_nonneg y]
    have hysquare : Real.sqrt (y ^ 2 + 3 / 4) ^ 2 = y ^ 2 + 3 / 4 :=
      Real.sq_sqrt hyq.le
    have hypos : 0 < y + Real.sqrt (y ^ 2 + 3 / 4) := by
      nlinarith [Real.sqrt_nonneg (y ^ 2 + 3 / 4)]
    rw [abs_of_pos hypos]
  have hlog := ((Real.hasDerivAt_log hpos.ne').comp z hsum').neg
  have hder :
      -((z + Real.sqrt (z ^ 2 + 3 / 4))⁻¹ *
          ((z + Real.sqrt (z ^ 2 + 3 / 4)) /
            Real.sqrt (z ^ 2 + 3 / 4))) =
        -1 / Real.sqrt (z ^ 2 + 3 / 4) := by
    change
      -((z + Real.sqrt (z ^ 2 + 3 / 4))⁻¹ *
          ((z + Real.sqrt (z ^ 2 + 3 / 4)) *
            (Real.sqrt (z ^ 2 + 3 / 4))⁻¹)) =
        (-1) * (Real.sqrt (z ^ 2 + 3 / 4))⁻¹
    calc
      -((z + Real.sqrt (z ^ 2 + 3 / 4))⁻¹ *
          ((z + Real.sqrt (z ^ 2 + 3 / 4)) *
            (Real.sqrt (z ^ 2 + 3 / 4))⁻¹)) =
          -((Real.sqrt (z ^ 2 + 3 / 4))⁻¹) := by
            rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
      _ = (-1) * (Real.sqrt (z ^ 2 + 3 / 4))⁻¹ := by ring
  rw [hder] at hlog
  unfold logSqrtPrimitive
  rw [habs]
  simpa only [Function.comp_apply] using hlog

private theorem positiveSubstitutionPrimitive_as_comp :
    positiveSubstitutionPrimitive =
      fun x => logSqrtPrimitive (1 / x + 1 / 2) := by
  funext x
  unfold positiveSubstitutionPrimitive logSqrtPrimitive
  rw [show (1 / x + 1 / 2) ^ 2 + 3 / 4 =
      (1 / x) ^ 2 + 1 / x + 1 by ring]

private theorem negativeSubstitutionPrimitive_as_comp :
    negativeSubstitutionPrimitive =
      fun x => logSqrtPrimitive (-1 / x - 1 / 2) := by
  funext x
  unfold negativeSubstitutionPrimitive logSqrtPrimitive
  rw [show (-1 / x - 1 / 2) ^ 2 + 3 / 4 =
      (-1 / x) ^ 2 - (-1 / x) + 1 by ring]

private theorem hasDerivAt_positiveSubstitutionPrimitive
    (x : ℝ) (hx : 0 < x) :
    HasDerivAt positiveSubstitutionPrimitive (integrand x) x := by
  have hx0 : x ≠ 0 := hx.ne'
  have hu : HasDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ 2) x := by
    convert (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx0 using 1 <;>
      simp only [id_eq] <;> field_simp [hx0] <;> ring
  have hz : HasDerivAt (fun y : ℝ => 1 / y + 1 / 2) (-1 / x ^ 2) x :=
    hu.add_const (1 / 2)
  have hc := (hasDerivAt_logSqrtPrimitive (1 / x + 1 / 2)).comp x hz
  have hq : 0 < x ^ 2 + x + 1 := by
    nlinarith [sq_nonneg (x + 1 / 2)]
  have ha : 0 < (1 / x + 1 / 2) ^ 2 + 3 / 4 := by positivity
  have halg : ((1 / x + 1 / 2) ^ 2 + 3 / 4) * x ^ 2 =
      x ^ 2 + x + 1 := by
    field_simp [hx0]
    ring
  have htrans :
      Real.sqrt ((1 / x + 1 / 2) ^ 2 + 3 / 4) * x =
        Real.sqrt (x ^ 2 + x + 1) :=
    sqrt_mul_eq_sqrt_of_mul_sq_eq
      ((1 / x + 1 / 2) ^ 2 + 3 / 4) (x ^ 2 + x + 1) x
      ha.le hq.le hx.le halg
  have hden :
      x * Real.sqrt (x ^ 2 + x + 1) =
        Real.sqrt ((1 / x + 1 / 2) ^ 2 + 3 / 4) * x ^ 2 := by
    rw [← htrans]
    ring
  rw [positiveSubstitutionPrimitive_as_comp]
  unfold integrand
  convert hc using 1
  rw [hden]
  field_simp [hx0, (Real.sqrt_pos.2 ha).ne']

private theorem hasDerivAt_negativeSubstitutionPrimitive
    (x : ℝ) (hx : x < 0) :
    HasDerivAt negativeSubstitutionPrimitive (integrand x) x := by
  have hx0 : x ≠ 0 := hx.ne
  have hu : HasDerivAt (fun y : ℝ => -1 / y) (1 / x ^ 2) x := by
    convert ((hasDerivAt_const x (-1 : ℝ)).div (hasDerivAt_id x) hx0) using 1 <;>
      simp only [id_eq] <;> field_simp [hx0] <;> ring
  have hz : HasDerivAt (fun y : ℝ => -1 / y - 1 / 2) (1 / x ^ 2) x :=
    hu.sub_const (1 / 2)
  have hc := (hasDerivAt_logSqrtPrimitive (-1 / x - 1 / 2)).comp x hz
  have hq : 0 < x ^ 2 + x + 1 := by
    nlinarith [sq_nonneg (x + 1 / 2)]
  have ha : 0 < (-1 / x - 1 / 2) ^ 2 + 3 / 4 := by positivity
  have halg : ((-1 / x - 1 / 2) ^ 2 + 3 / 4) * x ^ 2 =
      x ^ 2 + x + 1 := by
    field_simp [hx0]
    ring
  have halg' : ((-1 / x - 1 / 2) ^ 2 + 3 / 4) * (-x) ^ 2 =
      x ^ 2 + x + 1 := by
    calc
      ((-1 / x - 1 / 2) ^ 2 + 3 / 4) * (-x) ^ 2 =
          ((-1 / x - 1 / 2) ^ 2 + 3 / 4) * x ^ 2 := by ring
      _ = x ^ 2 + x + 1 := halg
  have htrans :
      Real.sqrt ((-1 / x - 1 / 2) ^ 2 + 3 / 4) * (-x) =
        Real.sqrt (x ^ 2 + x + 1) :=
    sqrt_mul_eq_sqrt_of_mul_sq_eq
      ((-1 / x - 1 / 2) ^ 2 + 3 / 4) (x ^ 2 + x + 1) (-x)
      ha.le hq.le (neg_nonneg.mpr hx.le) halg'
  have hden :
      x * Real.sqrt (x ^ 2 + x + 1) =
        -(Real.sqrt ((-1 / x - 1 / 2) ^ 2 + 3 / 4) * x ^ 2) := by
    rw [← htrans]
    ring
  rw [negativeSubstitutionPrimitive_as_comp]
  unfold integrand
  convert hc using 1
  rw [hden]
  field_simp [hx0, (Real.sqrt_pos.2 ha).ne']

private theorem antiderivativesOn_eq_primitiveFamilyOn_of_hasDerivAt
    (s : Set ℝ) (hsopen : IsOpen s) (hsconv : Convex ℝ s)
    (hsne : s.Nonempty) (g p : ℝ → ℝ)
    (hp : ∀ x ∈ s, HasDerivAt p (g x) x) :
    antiderivativesOn s g = primitiveFamilyOn s p := by
  ext F
  constructor
  · rintro ⟨hFd, hder⟩
    rcases hsne with ⟨a, ha⟩
    have hdiff : DifferentiableOn ℝ (fun x => F x - p x) s := by
      intro x hx
      have hFa : DifferentiableAt ℝ F x :=
        (hFd x hx).differentiableAt (hsopen.mem_nhds hx)
      exact (hFa.sub (hp x hx).differentiableAt).differentiableWithinAt
    have hzero : ∀ x ∈ s, deriv (fun y => F y - p y) x = 0 := by
      intro x hx
      have hFa : DifferentiableAt ℝ F x :=
        (hFd x hx).differentiableAt (hsopen.mem_nhds hx)
      have hd := (hFa.hasDerivAt.sub (hp x hx)).deriv
      simpa [hder x hx] using hd
    refine ⟨F a - p a, ?_⟩
    intro x hx
    have heq :=
      hsopen.is_const_of_deriv_eq_zero hsconv.isPreconnected hdiff hzero hx ha
    linarith
  · rintro ⟨C, hFC⟩
    have hhas : ∀ x ∈ s, HasDerivAt F (g x) x := by
      intro x hx
      have hev : Filter.EventuallyEq (nhds x) F (fun y => p y + C) := by
        filter_upwards [hsopen.mem_nhds hx] with y hy
        exact hFC y hy
      exact ((hp x hx).add_const C).congr_of_eventuallyEq hev
    constructor
    · intro x hx
      exact (hhas x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hhas x hx).deriv

private theorem primitiveFamilyOn_eq_of_additive_shift
    (s : Set ℝ) (p q : ℝ → ℝ)
    (h : ∃ K : ℝ, ∀ x ∈ s, p x = q x + K) :
    primitiveFamilyOn s p = primitiveFamilyOn s q := by
  rcases h with ⟨K, hK⟩
  ext F
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨K + C, ?_⟩
    intro x hx
    rw [hC x hx, hK x hx]
    ring
  · rintro ⟨C, hC⟩
    refine ⟨C - K, ?_⟩
    intro x hx
    rw [hC x hx, hK x hx]
    ring

private theorem positiveSubstitutionPrimitive_eq
    (x : ℝ) (hx : x ∈ positiveDomain) :
    positiveSubstitutionPrimitive x = positivePrimitive x + Real.log 2 := by
  have hx' : 0 < x := hx
  have hx0 : x ≠ 0 := hx'.ne'
  have hq : 0 < x ^ 2 + x + 1 := by
    nlinarith [sq_nonneg (x + 1 / 2)]
  have ha : 0 < (1 / x + 1 / 2) ^ 2 + 3 / 4 := by positivity
  have halg : ((1 / x + 1 / 2) ^ 2 + 3 / 4) * x ^ 2 =
      x ^ 2 + x + 1 := by
    field_simp [hx0]
    ring
  have htrans :
      Real.sqrt ((1 / x + 1 / 2) ^ 2 + 3 / 4) * x =
        Real.sqrt (x ^ 2 + x + 1) :=
    sqrt_mul_eq_sqrt_of_mul_sq_eq
      ((1 / x + 1 / 2) ^ 2 + 3 / 4) (x ^ 2 + x + 1) x
      ha.le hq.le hx'.le halg
  have hB : 0 < 1 / x + 1 / 2 +
      Real.sqrt ((1 / x + 1 / 2) ^ 2 + 3 / 4) := by
    have hs := Real.sq_sqrt ha.le
    nlinarith [Real.sqrt_nonneg ((1 / x + 1 / 2) ^ 2 + 3 / 4)]
  have hone : (1 / x) * x = 1 := by
    field_simp [hx0]
  have hrhs :
      2 * (1 / x + 1 / 2 +
        Real.sqrt ((1 / x + 1 / 2) ^ 2 + 3 / 4)) * x =
        x + 2 + 2 * Real.sqrt (x ^ 2 + x + 1) := by
    calc
      2 * (1 / x + 1 / 2 +
          Real.sqrt ((1 / x + 1 / 2) ^ 2 + 3 / 4)) * x =
          2 * ((1 / x) * x) + x +
            2 * (Real.sqrt ((1 / x + 1 / 2) ^ 2 + 3 / 4) * x) := by ring
      _ = x + 2 + 2 * Real.sqrt (x ^ 2 + x + 1) := by
        rw [hone, htrans]
        ring
  have harg :
      (x + 2 + 2 * Real.sqrt (x ^ 2 + x + 1)) / x =
        2 * (1 / x + 1 / 2 +
          Real.sqrt ((1 / x + 1 / 2) ^ 2 + 3 / 4)) :=
    (div_eq_iff hx0).2 hrhs.symm
  unfold positiveSubstitutionPrimitive positivePrimitive
  rw [show (1 / x) ^ 2 + 1 / x + 1 =
      (1 / x + 1 / 2) ^ 2 + 3 / 4 by ring]
  rw [Real.log_abs, Real.log_abs, harg,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hB.ne']
  ring

private theorem negativeSubstitutionPrimitive_eq
    (x : ℝ) (hx : x ∈ negativeDomain) :
    negativeSubstitutionPrimitive x = negativePrimitive x + Real.log 2 := by
  have hx' : x < 0 := hx
  have hx0 : x ≠ 0 := hx'.ne
  have hq : 0 < x ^ 2 + x + 1 := by
    nlinarith [sq_nonneg (x + 1 / 2)]
  have ha : 0 < (-1 / x - 1 / 2) ^ 2 + 3 / 4 := by positivity
  have halg : ((-1 / x - 1 / 2) ^ 2 + 3 / 4) * x ^ 2 =
      x ^ 2 + x + 1 := by
    field_simp [hx0]
    ring
  have halg' : ((-1 / x - 1 / 2) ^ 2 + 3 / 4) * (-x) ^ 2 =
      x ^ 2 + x + 1 := by
    calc
      ((-1 / x - 1 / 2) ^ 2 + 3 / 4) * (-x) ^ 2 =
          ((-1 / x - 1 / 2) ^ 2 + 3 / 4) * x ^ 2 := by ring
      _ = x ^ 2 + x + 1 := halg
  have htrans :
      Real.sqrt ((-1 / x - 1 / 2) ^ 2 + 3 / 4) * (-x) =
        Real.sqrt (x ^ 2 + x + 1) :=
    sqrt_mul_eq_sqrt_of_mul_sq_eq
      ((-1 / x - 1 / 2) ^ 2 + 3 / 4) (x ^ 2 + x + 1) (-x)
      ha.le hq.le (neg_nonneg.mpr hx'.le) halg'
  have hsx :
      Real.sqrt ((-1 / x - 1 / 2) ^ 2 + 3 / 4) * x =
        -Real.sqrt (x ^ 2 + x + 1) := by
    nlinarith
  have hB : 0 < -1 / x - 1 / 2 +
      Real.sqrt ((-1 / x - 1 / 2) ^ 2 + 3 / 4) := by
    have hs := Real.sq_sqrt ha.le
    nlinarith [Real.sqrt_nonneg ((-1 / x - 1 / 2) ^ 2 + 3 / 4)]
  have hone : (1 / x) * x = 1 := by
    field_simp [hx0]
  have hrhs :
      2 * (-1 / x - 1 / 2 +
        Real.sqrt ((-1 / x - 1 / 2) ^ 2 + 3 / 4)) * x =
        -x - 2 - 2 * Real.sqrt (x ^ 2 + x + 1) := by
    calc
      2 * (-1 / x - 1 / 2 +
          Real.sqrt ((-1 / x - 1 / 2) ^ 2 + 3 / 4)) * x =
          -2 * ((1 / x) * x) - x +
            2 * (Real.sqrt ((-1 / x - 1 / 2) ^ 2 + 3 / 4) * x) := by ring
      _ = -x - 2 - 2 * Real.sqrt (x ^ 2 + x + 1) := by
        rw [hone, hsx]
        ring
  have harg :
      (-x - 2 - 2 * Real.sqrt (x ^ 2 + x + 1)) / x =
        2 * (-1 / x - 1 / 2 +
          Real.sqrt ((-1 / x - 1 / 2) ^ 2 + 3 / 4)) :=
    (div_eq_iff hx0).2 hrhs.symm
  unfold negativeSubstitutionPrimitive negativePrimitive
  rw [show (-1 / x) ^ 2 - (-1 / x) + 1 =
      (-1 / x - 1 / 2) ^ 2 + 3 / 4 by ring]
  rw [Real.log_abs, Real.log_abs, harg,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hB.ne']
  ring

theorem gap1 (x t : ℝ) (hx : 0 < x) (ht : x = 1 / t) : 0 < t := by
  rw [ht] at hx
  exact one_div_pos.mp hx

theorem gap2 :
    antiderivativesOn positiveDomain integrand =
      antiderivativesOn positiveDomain
        (fun x => 1 / (x * Real.sqrt ((x + 1 / 2) ^ 2 + 3 / 4))) := by
  apply congrArg (antiderivativesOn positiveDomain)
  funext x
  unfold integrand
  rw [show (x + 1 / 2) ^ 2 + 3 / 4 = x ^ 2 + x + 1 by ring]

theorem gap3 :
    antiderivativesOn positiveDomain
        (fun x => 1 / (x * Real.sqrt ((x + 1 / 2) ^ 2 + 3 / 4))) =
      antiderivativesOn positiveDomain integrand := by
  exact gap2.symm

theorem gap4 :
    antiderivativesOn positiveDomain integrand =
      primitiveFamilyOn positiveDomain positiveSubstitutionPrimitive := by
  apply antiderivativesOn_eq_primitiveFamilyOn_of_hasDerivAt
  · exact isOpen_Ioi
  · exact convex_Ioi 0
  · refine ⟨1, ?_⟩
    change 0 < (1 : ℝ)
    norm_num
  · intro x hx
    exact hasDerivAt_positiveSubstitutionPrimitive x hx

theorem gap5 :
    primitiveFamilyOn positiveDomain positiveSubstitutionPrimitive =
      primitiveFamilyOn positiveDomain positivePrimitive := by
  apply primitiveFamilyOn_eq_of_additive_shift
  refine ⟨Real.log 2, ?_⟩
  intro x hx
  exact positiveSubstitutionPrimitive_eq x hx

theorem gap6 :
    antiderivativesOn positiveDomain integrand =
      primitiveFamilyOn positiveDomain positivePrimitive := by
  exact gap4.trans gap5

theorem gap7 :
    ∀ F, F ∈ antiderivativesOn positiveDomain integrand ↔
      ∃ C : ℝ, ∀ x ∈ positiveDomain, F x = positivePrimitive x + C := by
  intro F
  rw [gap6]
  rfl

theorem gap8 (x t : ℝ) (hx : x < 0) (ht : t = -1 / x) : 0 < t := by
  rw [ht]
  exact div_pos_of_neg_of_neg (by norm_num) hx

theorem gap9 :
    antiderivativesOn negativeDomain integrand =
      primitiveFamilyOn negativeDomain negativeSubstitutionPrimitive := by
  apply antiderivativesOn_eq_primitiveFamilyOn_of_hasDerivAt
  · exact isOpen_Iio
  · exact convex_Iio 0
  · refine ⟨-1, ?_⟩
    change (-1 : ℝ) < 0
    norm_num
  · intro x hx
    exact hasDerivAt_negativeSubstitutionPrimitive x hx

theorem gap10 :
    primitiveFamilyOn negativeDomain negativeSubstitutionPrimitive =
      primitiveFamilyOn negativeDomain negativePrimitive := by
  apply primitiveFamilyOn_eq_of_additive_shift
  refine ⟨Real.log 2, ?_⟩
  intro x hx
  exact negativeSubstitutionPrimitive_eq x hx

theorem gap11 :
    antiderivativesOn negativeDomain integrand =
      primitiveFamilyOn negativeDomain negativePrimitive := by
  exact gap9.trans gap10

theorem gap12 :
    (antiderivativesOn positiveDomain integrand =
        primitiveFamilyOn positiveDomain positivePrimitive) ∧
      (antiderivativesOn negativeDomain integrand =
        primitiveFamilyOn negativeDomain negativePrimitive) := by
  exact ⟨gap6, gap11⟩

end

end ProofGap.Exercise1856
