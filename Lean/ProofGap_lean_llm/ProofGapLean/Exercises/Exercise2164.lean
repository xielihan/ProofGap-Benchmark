import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2164

noncomputable section

def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}
def integrand (x : ℝ) := Real.sqrt (Real.tanh x ^ 2 + 1)
def rationalized (x : ℝ) :=
  (Real.tanh x ^ 2 + 1) / Real.sqrt (Real.tanh x ^ 2 + 1)
def hyperbolicRewrite (x : ℝ) :=
  ((Real.sinh x ^ 2 + Real.cosh x ^ 2) / Real.cosh x ^ 2) /
    Real.sqrt (Real.tanh x ^ 2 + 1)
def tanhPullback (x : ℝ) :=
  (2 * Real.cosh x ^ 2 - 1) /
    Real.sqrt (1 + Real.tanh x ^ 2) * deriv Real.tanh x
def SplitFamily : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
      (∀ x, HasDerivAt G
        (Real.cosh x ^ 2 * deriv Real.tanh x /
          Real.sqrt (1 + Real.tanh x ^ 2)) x) ∧
    ∃ H : ℝ → ℝ,
      (∀ x, HasDerivAt H
        (deriv Real.tanh x / Real.sqrt (1 + Real.tanh x ^ 2)) x) ∧
    ∀ x, F x = 2 * G x - H x}
def FirstReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives
      (fun x => 1 / Real.sqrt (Real.tanh x ^ 2 + 1)),
    ∀ x,
      F x = 2 * G x -
        Real.log (Real.tanh x + Real.sqrt (1 + Real.tanh x ^ 2))}
def SecondReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives
      (fun x => Real.cosh x /
        Real.sqrt (Real.sinh x ^ 2 + Real.cosh x ^ 2)),
    ∀ x,
      F x = 2 * G x -
        Real.log (Real.tanh x + Real.sqrt (1 + Real.tanh x ^ 2))}
def ThirdReductionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
      (∀ x, HasDerivAt G
        (deriv (fun y : ℝ => Real.sqrt 2 * Real.sinh y) x /
          Real.sqrt (1 + 2 * Real.sinh x ^ 2)) x) ∧
    ∀ x,
      F x = Real.sqrt 2 * G x -
        Real.log (Real.tanh x + Real.sqrt (1 + Real.tanh x ^ 2))}
def primitiveLong (x : ℝ) :=
  Real.sqrt 2 *
      Real.log (Real.sqrt 2 * Real.sinh x +
        Real.sqrt (1 + 2 * Real.sinh x ^ 2)) -
    Real.log (Real.tanh x + Real.sqrt (1 + Real.tanh x ^ 2))
def primitive (x : ℝ) :=
  1 / Real.sqrt 2 *
      Real.log ((Real.sqrt (1 + Real.tanh x ^ 2) +
          Real.sqrt 2 * Real.tanh x) /
        (Real.sqrt (1 + Real.tanh x ^ 2) -
          Real.sqrt 2 * Real.tanh x)) -
    Real.log (Real.tanh x + Real.sqrt (1 + Real.tanh x ^ 2))

private def pgH (x : ℝ) :=
  Real.log (Real.tanh x + Real.sqrt (1 + Real.tanh x ^ 2))

private def pgQ (x : ℝ) :=
  Real.log (Real.sqrt 2 * Real.sinh x +
    Real.sqrt (1 + 2 * Real.sinh x ^ 2))

private def pgG (x : ℝ) := pgQ x / Real.sqrt 2

private theorem pg_hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have heq : Real.tanh = fun y => Real.sinh y / Real.cosh y := by
    funext y
    exact Real.tanh_eq_sinh_div_cosh y
  rw [heq]
  convert (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc using 1
  field_simp [hc]
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

private theorem pg_hasDerivAt_logSqrt
    (v : ℝ → ℝ) (x v' : ℝ) (hv : HasDerivAt v v' x) :
    HasDerivAt
      (fun y => Real.log (v y + Real.sqrt (1 + v y ^ 2)))
      (v' / Real.sqrt (1 + v x ^ 2)) x := by
  have hrad : 0 < 1 + v x ^ 2 := by positivity
  have hspos : 0 < Real.sqrt (1 + v x ^ 2) := Real.sqrt_pos.2 hrad
  have hs_sq : Real.sqrt (1 + v x ^ 2) ^ 2 = 1 + v x ^ 2 :=
    Real.sq_sqrt hrad.le
  have harg : 0 < v x + Real.sqrt (1 + v x ^ 2) := by
    nlinarith [sq_nonneg (v x + Real.sqrt (1 + v x ^ 2))]
  have hu : HasDerivAt (fun y => 1 + v y ^ 2) (2 * v x * v') x := by
    simpa [mul_assoc] using (hv.pow 2).const_add 1
  have hsqrt :
      HasDerivAt (fun y => Real.sqrt (1 + v y ^ 2))
        (v x * v' / Real.sqrt (1 + v x ^ 2)) x := by
    have h := (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp x hu
    convert h using 1
    field_simp [ne_of_gt hspos]
  have h := (Real.hasDerivAt_log (ne_of_gt harg)).comp x (hv.add hsqrt)
  convert h using 1
  field_simp [ne_of_gt hspos, ne_of_gt harg]
  nlinarith

private theorem pg_hasDerivAt_H (x : ℝ) :
    HasDerivAt pgH
      (deriv Real.tanh x / Real.sqrt (1 + Real.tanh x ^ 2)) x := by
  have h := pg_hasDerivAt_logSqrt Real.tanh x
    (1 / Real.cosh x ^ 2) (pg_hasDerivAt_tanh x)
  simpa [pgH, (pg_hasDerivAt_tanh x).deriv] using h

private theorem pg_hasDerivAt_Q (x : ℝ) :
    HasDerivAt pgQ
      (deriv (fun y : ℝ => Real.sqrt 2 * Real.sinh y) x /
        Real.sqrt (1 + 2 * Real.sinh x ^ 2)) x := by
  have hv := (Real.hasDerivAt_sinh x).const_mul (Real.sqrt 2)
  have h := pg_hasDerivAt_logSqrt
    (fun y : ℝ => Real.sqrt 2 * Real.sinh y) x
    (Real.sqrt 2 * Real.cosh x) hv
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hrad (y : ℝ) :
      1 + (Real.sqrt 2 * Real.sinh y) ^ 2 =
        1 + 2 * Real.sinh y ^ 2 := by
    rw [mul_pow, hs]
  convert h using 1
  · funext y
    change Real.log (Real.sqrt 2 * Real.sinh y +
        Real.sqrt (1 + 2 * Real.sinh y ^ 2)) =
      Real.log (Real.sqrt 2 * Real.sinh y +
        Real.sqrt (1 + (Real.sqrt 2 * Real.sinh y) ^ 2))
    rw [hrad y]
  · rw [hv.deriv, hrad x]

private theorem pg_sqrt_relation (x : ℝ) :
    Real.sqrt (1 + Real.tanh x ^ 2) =
      Real.sqrt (1 + 2 * Real.sinh x ^ 2) / Real.cosh x := by
  have hc : 0 < Real.cosh x := Real.cosh_pos x
  have heq : (1 + Real.tanh x ^ 2) * Real.cosh x ^ 2 =
      1 + 2 * Real.sinh x ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [ne_of_gt hc]
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  have h₁ : Real.sqrt (1 + Real.tanh x ^ 2) ^ 2 =
      1 + Real.tanh x ^ 2 := Real.sq_sqrt (by positivity)
  have h₂ : Real.sqrt (1 + 2 * Real.sinh x ^ 2) ^ 2 =
      1 + 2 * Real.sinh x ^ 2 := Real.sq_sqrt (by positivity)
  have hprod :
      (Real.sqrt (1 + Real.tanh x ^ 2) * Real.cosh x) ^ 2 =
        Real.sqrt (1 + 2 * Real.sinh x ^ 2) ^ 2 := by
    calc
      (Real.sqrt (1 + Real.tanh x ^ 2) * Real.cosh x) ^ 2 =
          Real.sqrt (1 + Real.tanh x ^ 2) ^ 2 * Real.cosh x ^ 2 := by ring
      _ = (1 + Real.tanh x ^ 2) * Real.cosh x ^ 2 := by rw [h₁]
      _ = 1 + 2 * Real.sinh x ^ 2 := heq
      _ = Real.sqrt (1 + 2 * Real.sinh x ^ 2) ^ 2 := h₂.symm
  have hm : Real.sqrt (1 + Real.tanh x ^ 2) * Real.cosh x =
      Real.sqrt (1 + 2 * Real.sinh x ^ 2) := by
    have hn₁ : 0 ≤ Real.sqrt (1 + Real.tanh x ^ 2) * Real.cosh x := by positivity
    have hn₂ : 0 ≤ Real.sqrt (1 + 2 * Real.sinh x ^ 2) := Real.sqrt_nonneg _
    nlinarith [sq_nonneg
      (Real.sqrt (1 + Real.tanh x ^ 2) * Real.cosh x +
        Real.sqrt (1 + 2 * Real.sinh x ^ 2))]
  exact (eq_div_iff (ne_of_gt hc)).2 hm

private theorem pg_tanhPullback_value (x : ℝ) :
    integrand x = tanhPullback x := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hr : Real.sqrt (Real.tanh x ^ 2 + 1) ≠ 0 := by positivity
  have ht :
      (2 * Real.cosh x ^ 2 - 1) / Real.cosh x ^ 2 =
        Real.tanh x ^ 2 + 1 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [hc]
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  unfold integrand tanhPullback
  rw [(pg_hasDerivAt_tanh x).deriv]
  rw [show 1 + Real.tanh x ^ 2 = Real.tanh x ^ 2 + 1 by ring]
  symm
  calc
    (2 * Real.cosh x ^ 2 - 1) /
          Real.sqrt (Real.tanh x ^ 2 + 1) *
        (1 / Real.cosh x ^ 2) =
      ((2 * Real.cosh x ^ 2 - 1) / Real.cosh x ^ 2) /
        Real.sqrt (Real.tanh x ^ 2 + 1) := by
          simp only [div_eq_mul_inv, one_mul]
          ring
    _ = (Real.tanh x ^ 2 + 1) /
        Real.sqrt (Real.tanh x ^ 2 + 1) := by rw [ht]
    _ = Real.sqrt (Real.tanh x ^ 2 + 1) := by
      apply (div_eq_iff hr).2
      simpa [pow_two] using
        (Real.sq_sqrt (show 0 ≤ Real.tanh x ^ 2 + 1 by positivity)).symm

private theorem pg_first_reduction_value (x : ℝ) :
    Real.cosh x ^ 2 * deriv Real.tanh x /
        Real.sqrt (1 + Real.tanh x ^ 2) =
      1 / Real.sqrt (Real.tanh x ^ 2 + 1) := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hr : Real.sqrt (Real.tanh x ^ 2 + 1) ≠ 0 := by positivity
  rw [(pg_hasDerivAt_tanh x).deriv]
  rw [show 1 + Real.tanh x ^ 2 = Real.tanh x ^ 2 + 1 by ring]
  field_simp [hc, hr]

private theorem pg_first_value (x : ℝ) :
    Real.cosh x ^ 2 * deriv Real.tanh x /
        Real.sqrt (1 + Real.tanh x ^ 2) =
      Real.cosh x / Real.sqrt (1 + 2 * Real.sinh x ^ 2) := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hr : Real.sqrt (1 + 2 * Real.sinh x ^ 2) ≠ 0 := by positivity
  rw [(pg_hasDerivAt_tanh x).deriv, pg_sqrt_relation]
  field_simp [hc, hr]

private theorem pg_second_value (x : ℝ) :
    Real.cosh x / Real.sqrt (Real.sinh x ^ 2 + Real.cosh x ^ 2) =
      Real.cosh x / Real.sqrt (1 + 2 * Real.sinh x ^ 2) := by
  have hrad : Real.sinh x ^ 2 + Real.cosh x ^ 2 =
      1 + 2 * Real.sinh x ^ 2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  rw [hrad]

private theorem pg_second_reduction_value (x : ℝ) :
    Real.cosh x ^ 2 * deriv Real.tanh x /
        Real.sqrt (1 + Real.tanh x ^ 2) =
      Real.cosh x / Real.sqrt (Real.sinh x ^ 2 + Real.cosh x ^ 2) := by
  rw [pg_first_value, pg_second_value]

private theorem pg_hasDerivAt_G_first (x : ℝ) :
    HasDerivAt pgG
      (1 / Real.sqrt (Real.tanh x ^ 2 + 1)) x := by
  unfold pgG
  have h := (pg_hasDerivAt_Q x).div_const (Real.sqrt 2)
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hr : Real.sqrt (1 + 2 * Real.sinh x ^ 2) ≠ 0 := by positivity
  have hd : deriv (fun y : ℝ => Real.sqrt 2 * Real.sinh y) x =
      Real.sqrt 2 * Real.cosh x :=
    ((Real.hasDerivAt_sinh x).const_mul (Real.sqrt 2)).deriv
  rw [hd] at h
  convert h using 1
  rw [show Real.tanh x ^ 2 + 1 = 1 + Real.tanh x ^ 2 by ring]
  rw [pg_sqrt_relation]
  field_simp [hs, hc, hr]

private theorem pg_hasDerivAt_G_second (x : ℝ) :
    HasDerivAt pgG
      (Real.cosh x /
        Real.sqrt (Real.sinh x ^ 2 + Real.cosh x ^ 2)) x := by
  convert pg_hasDerivAt_G_first x using 1
  rw [← pg_first_reduction_value, pg_second_reduction_value]

private theorem pg_split_value (x : ℝ) :
    2 * (Real.cosh x ^ 2 * deriv Real.tanh x /
      Real.sqrt (1 + Real.tanh x ^ 2)) -
      deriv Real.tanh x / Real.sqrt (1 + Real.tanh x ^ 2) = integrand x := by
  rw [pg_tanhPullback_value]
  unfold tanhPullback
  ring

private theorem pg_third_value (x : ℝ) :
    Real.sqrt 2 *
        (deriv (fun y : ℝ => Real.sqrt 2 * Real.sinh y) x /
          Real.sqrt (1 + 2 * Real.sinh x ^ 2)) -
      deriv Real.tanh x / Real.sqrt (1 + Real.tanh x ^ 2) = integrand x := by
  have hd : deriv (fun y : ℝ => Real.sqrt 2 * Real.sinh y) x =
      Real.sqrt 2 * Real.cosh x :=
    ((Real.hasDerivAt_sinh x).const_mul (Real.sqrt 2)).deriv
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hmul : Real.sqrt 2 *
      (Real.sqrt 2 * Real.cosh x /
        Real.sqrt (1 + 2 * Real.sinh x ^ 2)) =
      2 * (Real.cosh x / Real.sqrt (1 + 2 * Real.sinh x ^ 2)) := by
    simp only [div_eq_mul_inv]
    calc
      Real.sqrt 2 * (Real.sqrt 2 * Real.cosh x *
          (Real.sqrt (1 + 2 * Real.sinh x ^ 2))⁻¹) =
        Real.sqrt 2 ^ 2 * Real.cosh x *
          (Real.sqrt (1 + 2 * Real.sinh x ^ 2))⁻¹ := by ring
      _ = 2 * (Real.cosh x *
          (Real.sqrt (1 + 2 * Real.sinh x ^ 2))⁻¹) := by
        rw [hs]
        ring
  rw [hd, hmul, ← pg_first_value]
  exact pg_split_value x

private theorem pg_hasDerivAt_primitiveLong (x : ℝ) :
    HasDerivAt primitiveLong (integrand x) x := by
  have heq : primitiveLong =
      fun y => Real.sqrt 2 * pgQ y - pgH y := by rfl
  rw [heq]
  have h := ((pg_hasDerivAt_Q x).const_mul (Real.sqrt 2)).sub
    (pg_hasDerivAt_H x)
  convert h using 1
  exact (pg_third_value x).symm

private theorem pg_primitive_decomposition (x : ℝ) :
    primitiveLong x = 2 * pgG x - pgH x := by
  change Real.sqrt 2 * pgQ x - pgH x = 2 * pgG x - pgH x
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hs2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hinv : 2 / Real.sqrt 2 = Real.sqrt 2 := by
    apply (div_eq_iff hs).2
    simpa [pow_two] using hs2.symm
  have hcoef : Real.sqrt 2 * pgQ x = 2 * pgG x := by
    unfold pgG
    calc
      Real.sqrt 2 * pgQ x = (2 / Real.sqrt 2) * pgQ x := by rw [hinv]
      _ = 2 * (pgQ x / Real.sqrt 2) := by ring
  rw [hcoef]

private theorem pg_antiderivative_representation
    (f p : ℝ → ℝ) (hp : ∀ x, HasDerivAt p (f x) x)
    (F : ℝ → ℝ) (hF : F ∈ Antiderivatives f) :
    ∃ C : ℝ, ∀ x, F x = p x + C := by
  change ∀ x, HasDerivAt F (f x) x at hF
  refine ⟨F 0 - p 0, ?_⟩
  intro x
  have hc : F x - p x = F 0 - p 0 := by
    apply is_const_of_deriv_eq_zero
      (fun z => ((hF z).sub (hp z)).differentiableAt)
      (fun z => by simpa using ((hF z).sub (hp z)).deriv)
  linarith

private theorem pg_antiderivatives_eq_primitiveFamily
    (f p : ℝ → ℝ) (hp : ∀ x, HasDerivAt p (f x) x) :
    Antiderivatives f = PrimitiveFamily p := by
  ext F
  constructor
  · exact pg_antiderivative_representation f p hp F
  · rintro ⟨C, hC⟩
    change ∀ x, HasDerivAt F (f x) x
    intro x
    have heq : F = fun y => p y + C := funext hC
    rw [heq]
    exact (hp x).add_const C

private theorem pg_ratio_identity (x : ℝ) :
    (Real.sqrt (1 + Real.tanh x ^ 2) + Real.sqrt 2 * Real.tanh x) /
        (Real.sqrt (1 + Real.tanh x ^ 2) - Real.sqrt 2 * Real.tanh x) =
      (Real.sqrt 2 * Real.sinh x +
        Real.sqrt (1 + 2 * Real.sinh x ^ 2)) ^ 2 := by
  have hc : 0 < Real.cosh x := Real.cosh_pos x
  have hs2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hA : Real.sqrt (1 + 2 * Real.sinh x ^ 2) ^ 2 =
      1 + 2 * Real.sinh x ^ 2 := Real.sq_sqrt (by positivity)
  have hminus : Real.sqrt (1 + 2 * Real.sinh x ^ 2) -
      Real.sqrt 2 * Real.sinh x > 0 := by
    have hn := Real.sqrt_nonneg (1 + 2 * Real.sinh x ^ 2)
    nlinarith [sq_nonneg
      (Real.sqrt (1 + 2 * Real.sinh x ^ 2) +
        Real.sqrt 2 * Real.sinh x)]
  have hprod :
      (Real.sqrt (1 + 2 * Real.sinh x ^ 2) -
          Real.sqrt 2 * Real.sinh x) *
        (Real.sqrt (1 + 2 * Real.sinh x ^ 2) +
          Real.sqrt 2 * Real.sinh x) = 1 := by
    nlinarith
  have hratio :
      (Real.sqrt (1 + 2 * Real.sinh x ^ 2) +
          Real.sqrt 2 * Real.sinh x) /
        (Real.sqrt (1 + 2 * Real.sinh x ^ 2) -
          Real.sqrt 2 * Real.sinh x) =
      (Real.sqrt (1 + 2 * Real.sinh x ^ 2) +
          Real.sqrt 2 * Real.sinh x) ^ 2 := by
    apply (div_eq_iff (ne_of_gt hminus)).2
    calc
      Real.sqrt (1 + 2 * Real.sinh x ^ 2) +
          Real.sqrt 2 * Real.sinh x =
        (Real.sqrt (1 + 2 * Real.sinh x ^ 2) +
          Real.sqrt 2 * Real.sinh x) * 1 := by ring
      _ = (Real.sqrt (1 + 2 * Real.sinh x ^ 2) +
          Real.sqrt 2 * Real.sinh x) *
          ((Real.sqrt (1 + 2 * Real.sinh x ^ 2) -
              Real.sqrt 2 * Real.sinh x) *
            (Real.sqrt (1 + 2 * Real.sinh x ^ 2) +
              Real.sqrt 2 * Real.sinh x)) := by rw [hprod]
      _ = (Real.sqrt (1 + 2 * Real.sinh x ^ 2) +
          Real.sqrt 2 * Real.sinh x) ^ 2 *
          (Real.sqrt (1 + 2 * Real.sinh x ^ 2) -
            Real.sqrt 2 * Real.sinh x) := by ring
  have hleft :
      (Real.sqrt (1 + Real.tanh x ^ 2) + Real.sqrt 2 * Real.tanh x) /
          (Real.sqrt (1 + Real.tanh x ^ 2) - Real.sqrt 2 * Real.tanh x) =
        (Real.sqrt (1 + 2 * Real.sinh x ^ 2) +
            Real.sqrt 2 * Real.sinh x) /
          (Real.sqrt (1 + 2 * Real.sinh x ^ 2) -
            Real.sqrt 2 * Real.sinh x) := by
    rw [pg_sqrt_relation, Real.tanh_eq_sinh_div_cosh]
    field_simp [ne_of_gt hc, ne_of_gt hminus]
  rw [hleft, hratio]
  congr 1
  ring

private theorem pg_primitive_eq_long : primitive = primitiveLong := by
  funext x
  unfold primitive
  rw [pg_ratio_identity]
  unfold primitiveLong
  rw [Real.log_pow]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hs2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hinv : 2 / Real.sqrt 2 = Real.sqrt 2 := by
    apply (div_eq_iff hs).2
    simpa [pow_two] using hs2.symm
  have hcoef (z : ℝ) :
      1 / Real.sqrt 2 * (2 * z) = Real.sqrt 2 * z := by
    calc
      1 / Real.sqrt 2 * (2 * z) = (2 / Real.sqrt 2) * z := by ring
      _ = Real.sqrt 2 * z := by rw [hinv]
  simpa using hcoef (Real.log (Real.sqrt 2 * Real.sinh x +
    Real.sqrt (1 + 2 * Real.sinh x ^ 2)))

theorem gap1 :
    Antiderivatives integrand = Antiderivatives rationalized := by
  apply congrArg Antiderivatives
  funext x
  unfold integrand rationalized
  have hpos : 0 < Real.tanh x ^ 2 + 1 := by positivity
  apply (eq_div_iff (Real.sqrt_ne_zero'.mpr hpos)).2
  exact Real.mul_self_sqrt hpos.le
theorem gap2 :
    Antiderivatives integrand = Antiderivatives hyperbolicRewrite := by
  rw [gap1]
  apply congrArg Antiderivatives
  funext x
  unfold rationalized hyperbolicRewrite
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hr : Real.sqrt (Real.tanh x ^ 2 + 1) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    positivity
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hc, hr]
  <;> ring
theorem gap3 :
    Antiderivatives integrand = Antiderivatives tanhPullback := by
  apply congrArg Antiderivatives
  funext x
  exact pg_tanhPullback_value x
theorem gap4 :
    Antiderivatives integrand = SplitFamily := by
  rw [pg_antiderivatives_eq_primitiveFamily integrand primitiveLong pg_hasDerivAt_primitiveLong]
  ext F
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨fun x => pgG x + C / 2, ?_, fun x => pgH x, ?_, ?_⟩
    · intro x
      simpa [pg_first_reduction_value x] using
        (pg_hasDerivAt_G_first x).add_const (C / 2)
    · intro x
      exact pg_hasDerivAt_H x
    · intro x
      rw [hC x, pg_primitive_decomposition]
      ring
  · rintro ⟨G, hG, H, hH, hF⟩
    refine ⟨F 0 - primitiveLong 0, ?_⟩
    have hanti : F ∈ Antiderivatives integrand := by
      change ∀ x, HasDerivAt F (integrand x) x
      intro x
      have heq : F = fun y => 2 * G y - H y := funext hF
      rw [heq]
      have hd := ((hG x).const_mul 2).sub (hH x)
      convert hd using 1
      exact (pg_split_value x).symm
    rcases pg_antiderivative_representation integrand primitiveLong
      pg_hasDerivAt_primitiveLong F hanti with ⟨C, hC⟩
    intro x
    have h0 := hC 0
    have hx := hC x
    linarith
theorem gap5 :
    Antiderivatives integrand = FirstReductionFamily := by
  rw [pg_antiderivatives_eq_primitiveFamily integrand primitiveLong pg_hasDerivAt_primitiveLong]
  ext F
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨fun x => pgG x + C / 2, ?_, ?_⟩
    · intro x
      exact (pg_hasDerivAt_G_first x).add_const (C / 2)
    · intro x
      rw [hC x, pg_primitive_decomposition]
      unfold pgH
      ring
  · rintro ⟨G, hG, hF⟩
    refine ⟨F 0 - primitiveLong 0, ?_⟩
    have hanti : F ∈ Antiderivatives integrand := by
      change ∀ x, HasDerivAt F (integrand x) x
      intro x
      have heq : F = fun y => 2 * G y - pgH y := by
        funext y
        simpa [pgH] using hF y
      rw [heq]
      have hd := ((hG x).const_mul 2).sub (pg_hasDerivAt_H x)
      convert hd using 1
      simpa [pg_first_reduction_value x] using (pg_split_value x).symm
    rcases pg_antiderivative_representation integrand primitiveLong
      pg_hasDerivAt_primitiveLong F hanti with ⟨C, hC⟩
    intro x
    have h0 := hC 0
    have hx := hC x
    linarith
theorem gap6 :
    Antiderivatives integrand = SecondReductionFamily := by
  rw [pg_antiderivatives_eq_primitiveFamily integrand primitiveLong pg_hasDerivAt_primitiveLong]
  ext F
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨fun x => pgG x + C / 2, ?_, ?_⟩
    · intro x
      exact (pg_hasDerivAt_G_second x).add_const (C / 2)
    · intro x
      rw [hC x, pg_primitive_decomposition]
      unfold pgH
      ring
  · rintro ⟨G, hG, hF⟩
    refine ⟨F 0 - primitiveLong 0, ?_⟩
    have hanti : F ∈ Antiderivatives integrand := by
      change ∀ x, HasDerivAt F (integrand x) x
      intro x
      have heq : F = fun y => 2 * G y - pgH y := by
        funext y
        simpa [pgH] using hF y
      rw [heq]
      have hd := ((hG x).const_mul 2).sub (pg_hasDerivAt_H x)
      convert hd using 1
      simpa [pg_second_reduction_value x] using (pg_split_value x).symm
    rcases pg_antiderivative_representation integrand primitiveLong
      pg_hasDerivAt_primitiveLong F hanti with ⟨C, hC⟩
    intro x
    have h0 := hC 0
    have hx := hC x
    linarith
theorem gap7 :
    Antiderivatives integrand = ThirdReductionFamily := by
  rw [pg_antiderivatives_eq_primitiveFamily integrand primitiveLong pg_hasDerivAt_primitiveLong]
  ext F
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨fun x => pgQ x + C / Real.sqrt 2, ?_, ?_⟩
    · intro x
      exact (pg_hasDerivAt_Q x).add_const (C / Real.sqrt 2)
    · intro x
      rw [hC x]
      change Real.sqrt 2 * pgQ x - pgH x + C =
        Real.sqrt 2 * (pgQ x + C / Real.sqrt 2) - pgH x
      have hs : Real.sqrt 2 ≠ 0 := by positivity
      field_simp [hs]
      ring
  · rintro ⟨G, hG, hF⟩
    refine ⟨F 0 - primitiveLong 0, ?_⟩
    have hanti : F ∈ Antiderivatives integrand := by
      change ∀ x, HasDerivAt F (integrand x) x
      intro x
      have heq : F = fun y => Real.sqrt 2 * G y - pgH y := by
        funext y
        simpa [pgH] using hF y
      rw [heq]
      have hd := ((hG x).const_mul (Real.sqrt 2)).sub (pg_hasDerivAt_H x)
      convert hd using 1
      exact (pg_third_value x).symm
    rcases pg_antiderivative_representation integrand primitiveLong
      pg_hasDerivAt_primitiveLong F hanti with ⟨C, hC⟩
    intro x
    have h0 := hC 0
    have hx := hC x
    linarith
theorem gap8 :
    Antiderivatives integrand = PrimitiveFamily primitiveLong := by
  exact pg_antiderivatives_eq_primitiveFamily integrand primitiveLong
    pg_hasDerivAt_primitiveLong
theorem gap9 :
    Antiderivatives integrand = PrimitiveFamily primitive := by
  rw [gap8]
  apply congrArg PrimitiveFamily
  exact pg_primitive_eq_long.symm

end
end ProofGap.Exercise2164
