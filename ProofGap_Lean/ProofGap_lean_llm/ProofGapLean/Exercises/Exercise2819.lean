import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Stirling

namespace ProofGap.Exercise2819

noncomputable section

open Filter
open scoped BigOperators Topology

def base (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ n * (Nat.factorial n : ℝ) ^ 2) /
    Nat.factorial (2 * n + 1)

def coefficient (p : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * Real.rpow (base n) p

def radius (p : ℝ) : ℝ :=
  Real.rpow 2 p

def powerTerm (p : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  coefficient p n * x ^ n

def SeriesConvergesAt (p x : ℝ) : Prop :=
  Summable (fun k : ℕ => powerTerm p (k + 1) x)

def HasConvergenceRadius (p : ℝ) : Prop :=
  (∀ x : ℝ, |x| < radius p → SeriesConvergesAt p x) ∧
    (∀ x : ℝ, radius p < |x| → ¬ SeriesConvergesAt p x)

def endpointMagnitude (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow
    (((4 : ℝ) ^ n * (Nat.factorial n : ℝ) ^ 2) /
      Nat.factorial (2 * n + 1)) p

def radiusRatio (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (((2 * n + 3 : ℕ) : ℝ) / (n + 1 : ℝ)) p

def endpointRatio (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (((2 * n + 3 : ℕ) : ℝ) / ((2 * n + 2 : ℕ) : ℝ)) p

def forwardEndpointRatio (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ)) p

def raabeSeq (p : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (endpointMagnitude p n / endpointMagnitude p (n + 1) - 1)

def asymptoticModel (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (Real.pi / (4 * (n : ℝ))) (p / 2)

def ConditionallySummable (u : ℕ → ℝ) : Prop :=
  ProofGap.SeriesConverges u ∧ ¬ Summable (fun n => |u n|)

private def endpointBase (n : ℕ) : ℝ :=
  ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) ^ 2) /
    Nat.factorial (2 * n + 1)

private def centralEndpoint (n : ℕ) : ℝ :=
  ((Nat.factorial n : ℝ) ^ 2 / Nat.factorial (2 * n)) * (4 : ℝ) ^ n

private theorem base_pos (n : ℕ) : 0 < base n := by
  unfold base
  positivity

private theorem endpointBase_pos (n : ℕ) : 0 < endpointBase n := by
  unfold endpointBase
  positivity

private theorem endpointMagnitude_pos (p : ℝ) (n : ℕ) :
    0 < endpointMagnitude p n := by
  unfold endpointMagnitude
  exact Real.rpow_pos_of_pos (endpointBase_pos n) p

private theorem centralEndpoint_pos (n : ℕ) : 0 < centralEndpoint n := by
  unfold centralEndpoint
  positivity

private theorem central_stirling_identity (m : ℕ) (hm : m ≠ 0) :
    centralEndpoint m / Real.sqrt (Real.pi * (m : ℝ)) =
      Stirling.stirlingSeq m ^ 2 /
        (Stirling.stirlingSeq (2 * m) * Real.sqrt Real.pi) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero hm)
  unfold centralEndpoint Stirling.stirlingSeq
  push_cast
  field_simp
  rw [Real.sq_sqrt (by positivity)]
  rw [Real.sqrt_mul (le_of_lt Real.pi_pos)]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (m : ℝ))]
  norm_num
  rw [show (((m : ℝ) / Real.exp 1) ^ m) ^ 2 =
      ((m : ℝ) / Real.exp 1) ^ (2 * m) by
        rw [← pow_mul]
        congr 1
        omega]
  rw [show (m : ℝ) * 2 / Real.exp 1 =
      2 * ((m : ℝ) / Real.exp 1) by ring]
  rw [mul_pow]
  rw [show (2 : ℝ) ^ (2 * m) = 4 ^ m by
    rw [pow_mul]
    norm_num]
  ring_nf
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ))]
  rw [show Real.sqrt (4 : ℝ) = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)]
  ring

private theorem endpointBase_eq_central (m : ℕ) :
    endpointBase m = centralEndpoint m / (((2 * m + 1 : ℕ) : ℝ)) := by
  unfold endpointBase centralEndpoint
  rw [show 2 * m + 1 = (2 * m) + 1 by omega, Nat.factorial_succ]
  push_cast
  field_simp

private theorem endpoint_stirling_identity (m : ℕ) (hm : m ≠ 0) :
    endpointBase m /
        Real.sqrt (Real.pi / (4 * (m : ℝ))) =
      (Stirling.stirlingSeq m ^ 2 /
          (Stirling.stirlingSeq (2 * m) * Real.sqrt Real.pi)) *
        (((2 * m : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hsmall : 0 < Real.sqrt (Real.pi / (4 * (m : ℝ))) := by positivity
  have hroot :
      Real.sqrt (Real.pi * (m : ℝ)) =
        (2 * (m : ℝ)) * Real.sqrt (Real.pi / (4 * (m : ℝ))) := by
    have hsquare :
        ((2 * (m : ℝ)) * Real.sqrt (Real.pi / (4 * (m : ℝ)))) ^ 2 =
          Real.pi * (m : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      field_simp [hmR.ne']
      ring
    have hleft := Real.sq_sqrt (by positivity : 0 ≤ Real.pi * (m : ℝ))
    have hleft_nonneg := Real.sqrt_nonneg (Real.pi * (m : ℝ))
    have hright_nonneg :
        0 ≤ (2 * (m : ℝ)) * Real.sqrt (Real.pi / (4 * (m : ℝ))) := by
      positivity
    nlinarith
  calc
    endpointBase m / Real.sqrt (Real.pi / (4 * (m : ℝ))) =
        (centralEndpoint m / Real.sqrt (Real.pi * (m : ℝ))) *
          (((2 * m : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) := by
      rw [endpointBase_eq_central, hroot]
      have hden : (((2 * m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp [hsmall.ne', hmR.ne', hden]
      push_cast
      ring
    _ = (Stirling.stirlingSeq m ^ 2 /
          (Stirling.stirlingSeq (2 * m) * Real.sqrt Real.pi)) *
        (((2 * m : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) := by
      rw [central_stirling_identity m hm]

private theorem endpointBase_asymptotic :
    Tendsto
      (fun n : ℕ =>
        endpointBase (n + 1) /
          Real.sqrt (Real.pi / (4 * (((n + 1 : ℕ) : ℝ)))))
      atTop (𝓝 1) := by
  have hs₁ :
      Tendsto (fun n : ℕ => Stirling.stirlingSeq (n + 1))
        atTop (𝓝 (Real.sqrt Real.pi)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)
  have hidx : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    refine tendsto_atTop.2 (fun b => ?_)
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hs₂ :
      Tendsto (fun n : ℕ => Stirling.stirlingSeq (2 * (n + 1)))
        atTop (𝓝 (Real.sqrt Real.pi)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp hidx
  have hsqrt : Real.sqrt Real.pi ≠ 0 := by positivity
  have hstirling :
      Tendsto
        (fun n : ℕ =>
          Stirling.stirlingSeq (n + 1) ^ 2 /
            (Stirling.stirlingSeq (2 * (n + 1)) * Real.sqrt Real.pi))
        atTop (𝓝 1) := by
    have hratio :=
      (hs₁.mul hs₁).div (hs₂.mul tendsto_const_nhds)
        (mul_ne_zero hsqrt hsqrt)
    convert hratio using 1
    · funext n
      simp only [pow_two, Pi.div_apply]
    · rw [Real.mul_self_sqrt Real.pi_nonneg]
      field_simp [Real.pi_ne_zero]
  have hrat :
      Tendsto
        (fun n : ℕ =>
          (((2 * (n + 1) : ℕ) : ℝ) / ((2 * (n + 1) + 1 : ℕ) : ℝ)))
        atTop (𝓝 1) := by
    convert (tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1).comp hidx using 1
    funext n
    simp [Function.comp_apply]
  have hprod := hstirling.mul hrat
  convert hprod using 1
  · funext n
    rw [endpoint_stirling_identity (n + 1) (by omega)]
  · norm_num

private theorem endpointMagnitude_asymptotic (p : ℝ) :
    Tendsto
      (fun n : ℕ =>
        endpointMagnitude p (n + 1) / asymptoticModel p (n + 1))
      atTop (𝓝 1) := by
  have hrpow := endpointBase_asymptotic.rpow_const (p := p) (Or.inl one_ne_zero)
  convert hrpow using 1
  · funext n
    have ha :
        0 ≤ Real.pi / (4 * (((n + 1 : ℕ) : ℝ))) := by positivity
    have hsqrt :
        0 ≤ Real.sqrt (Real.pi / (4 * (((n + 1 : ℕ) : ℝ)))) :=
      Real.sqrt_nonneg _
    change
      Real.rpow (endpointBase (n + 1)) p /
          Real.rpow (Real.pi / (4 * (((n + 1 : ℕ) : ℝ)))) (p / 2) =
        Real.rpow
          (endpointBase (n + 1) /
            Real.sqrt (Real.pi / (4 * (((n + 1 : ℕ) : ℝ))))) p
    calc
      Real.rpow (endpointBase (n + 1)) p /
          Real.rpow (Real.pi / (4 * (((n + 1 : ℕ) : ℝ)))) (p / 2) =
          Real.rpow (endpointBase (n + 1)) p /
            Real.rpow
              (Real.sqrt (Real.pi / (4 * (((n + 1 : ℕ) : ℝ))))) p := by
        exact congrArg
          (fun z : ℝ => Real.rpow (endpointBase (n + 1)) p / z)
          (Real.rpow_div_two_eq_sqrt p ha)
      _ = Real.rpow
          (endpointBase (n + 1) /
            Real.sqrt (Real.pi / (4 * (((n + 1 : ℕ) : ℝ))))) p :=
        (Real.div_rpow (endpointBase_pos _).le hsqrt p).symm
  · simp

private theorem endpointMagnitude_isEquivalent (p : ℝ) :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => endpointMagnitude p (n + 1))
      (fun n : ℕ => asymptoticModel p (n + 1)) :=
  Asymptotics.isEquivalent_of_tendsto_one (endpointMagnitude_asymptotic p)

private theorem asymptoticModel_eq (p : ℝ) (n : ℕ) (hn : n ≠ 0) :
    asymptoticModel p n =
      Real.rpow (Real.pi / 4) (p / 2) *
        Real.rpow (n : ℝ) (-(p / 2)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hbase :
      Real.pi / (4 * (n : ℝ)) = (Real.pi / 4) / (n : ℝ) := by
    field_simp [hnR.ne']
  unfold asymptoticModel
  calc
    Real.rpow (Real.pi / (4 * (n : ℝ))) (p / 2) =
        Real.rpow ((Real.pi / 4) / (n : ℝ)) (p / 2) := by
      rw [hbase]
    _ = Real.rpow (Real.pi / 4) (p / 2) /
        Real.rpow (n : ℝ) (p / 2) :=
      Real.div_rpow (by positivity) hnR.le (p / 2)
    _ = Real.rpow (Real.pi / 4) (p / 2) *
        Real.rpow (n : ℝ) (-(p / 2)) := by
      exact congrArg
        (fun z : ℝ => Real.rpow (Real.pi / 4) (p / 2) * z)
        (Real.rpow_neg hnR.le (p / 2)).symm

private theorem asymptoticModel_summable_iff (p : ℝ) :
    Summable (fun n : ℕ => asymptoticModel p (n + 1)) ↔ 2 < p := by
  let c : ℝ := Real.rpow (Real.pi / 4) (p / 2)
  have hc : 0 < c := by
    dsimp [c]
    exact Real.rpow_pos_of_pos (by positivity) _
  have heq :
      (fun n : ℕ => asymptoticModel p (n + 1)) =
        fun n : ℕ => c * Real.rpow (((n + 1 : ℕ) : ℝ)) (-(p / 2)) := by
    funext n
    exact asymptoticModel_eq p (n + 1) (by omega)
  rw [heq]
  constructor
  · intro hs
    have hi := hs.mul_left c⁻¹
    have hpow :
        Summable (fun n : ℕ => Real.rpow (((n + 1 : ℕ) : ℝ)) (-(p / 2))) := by
      refine hi.congr ?_
      intro n
      field_simp [hc.ne']
    have hall :
        Summable (fun n : ℕ => Real.rpow (n : ℝ) (-(p / 2))) :=
      (summable_nat_add_iff 1).1 hpow
    have hexp := (Real.summable_nat_rpow (p := -(p / 2))).1 hall
    linarith
  · intro hp
    have hall :
        Summable (fun n : ℕ => Real.rpow (n : ℝ) (-(p / 2))) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have hshift :
        Summable (fun n : ℕ => Real.rpow (((n + 1 : ℕ) : ℝ)) (-(p / 2))) :=
      (summable_nat_add_iff 1).2 hall
    exact hshift.mul_left c

private theorem asymptoticModel_tendsto_zero (p : ℝ) (hp : 0 < p) :
    Tendsto (fun n : ℕ => asymptoticModel p (n + 1)) atTop (𝓝 0) := by
  have hcast :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hpow :
      Tendsto (fun n : ℕ => Real.rpow (((n + 1 : ℕ) : ℝ)) (-(p / 2)))
        atTop (𝓝 0) := by
    have hp2 : 0 < p / 2 := by linarith
    exact tendsto_rpow_neg_atTop hp2 |>.comp hcast
  have hmul :=
    (tendsto_const_nhds (x := Real.rpow (Real.pi / 4) (p / 2))).mul hpow
  convert hmul using 1
  · funext n
    rw [asymptoticModel_eq p (n + 1) (by omega)]
  · ring

private theorem coefficient_ne (p : ℝ) (n : ℕ) : coefficient p n ≠ 0 := by
  unfold coefficient
  exact mul_ne_zero (pow_ne_zero _ (by norm_num))
    (Real.rpow_pos_of_pos (base_pos n) p).ne'

private theorem coefficient_abs (p : ℝ) (n : ℕ) :
    |coefficient p n| = Real.rpow (base n) p := by
  simp [coefficient, abs_of_nonneg (Real.rpow_nonneg (base_pos n).le p)]

private theorem base_succ (n : ℕ) :
    base (n + 1) =
      base n * (((n + 1 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ)) := by
  have hfacn :
      ((Nat.factorial (n + 1) : ℕ) : ℝ) =
        ((n + 1 : ℕ) : ℝ) * (Nat.factorial n : ℝ) := by
    rw [Nat.factorial_succ]
    norm_num
  have hfac2 :
      ((Nat.factorial (2 * (n + 1) + 1) : ℕ) : ℝ) =
        ((2 * n + 3 : ℕ) : ℝ) * ((2 * n + 2 : ℕ) : ℝ) *
          (Nat.factorial (2 * n + 1) : ℝ) := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 2) + 1 by omega,
      Nat.factorial_succ,
      show 2 * n + 2 = (2 * n + 1) + 1 by omega,
      Nat.factorial_succ]
    push_cast
    ring
  unfold base
  rw [hfacn, hfac2]
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hf : (0 : ℝ) < (Nat.factorial (2 * n + 1) : ℝ) := by positivity
  field_simp [hn1.ne', hf.ne']
  push_cast
  ring

private theorem endpointBase_succ (n : ℕ) :
    endpointBase (n + 1) =
      endpointBase n *
        (((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ)) := by
  have hfacn :
      ((Nat.factorial (n + 1) : ℕ) : ℝ) =
        ((n + 1 : ℕ) : ℝ) * (Nat.factorial n : ℝ) := by
    rw [Nat.factorial_succ]
    norm_num
  have hfac2 :
      ((Nat.factorial (2 * (n + 1) + 1) : ℕ) : ℝ) =
        ((2 * n + 3 : ℕ) : ℝ) * ((2 * n + 2 : ℕ) : ℝ) *
          (Nat.factorial (2 * n + 1) : ℝ) := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 2) + 1 by omega,
      Nat.factorial_succ,
      show 2 * n + 2 = (2 * n + 1) + 1 by omega,
      Nat.factorial_succ]
    push_cast
    ring
  unfold endpointBase
  rw [hfacn, hfac2]
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hf : (0 : ℝ) < (Nat.factorial (2 * n + 1) : ℝ) := by positivity
  field_simp [hn1.ne', hf.ne']
  push_cast
  ring

private theorem base_ratio (n : ℕ) :
    base n / base (n + 1) =
      ((2 * n + 3 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  rw [base_succ]
  have hb : base n ≠ 0 := (base_pos n).ne'
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have h2n : (((2 * n + 3 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hb, hn, h2n]

private theorem endpointBase_ratio (n : ℕ) :
    endpointBase n / endpointBase (n + 1) =
      ((2 * n + 3 : ℕ) : ℝ) / ((2 * n + 2 : ℕ) : ℝ) := by
  rw [endpointBase_succ]
  have hb : endpointBase n ≠ 0 := (endpointBase_pos n).ne'
  have h2 : (((2 * n + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  have h3 : (((2 * n + 3 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hb, h2, h3]

private theorem endpointBase_forward_ratio (n : ℕ) :
    endpointBase (n + 1) / endpointBase n =
      ((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ) := by
  rw [endpointBase_succ]
  field_simp [(endpointBase_pos n).ne']

private theorem endpointMagnitude_eq (p : ℝ) (n : ℕ) :
    endpointMagnitude p n = Real.rpow (endpointBase n) p := by
  rfl

private theorem endpointBase_eq (n : ℕ) :
    endpointBase n = base n * (2 : ℝ) ^ n := by
  unfold endpointBase base
  have hf : (Nat.factorial (2 * n + 1) : ℝ) ≠ 0 := by positivity
  rw [show (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n by
    rw [← mul_pow]
    norm_num]
  field_simp [hf]

private theorem powerTerm_ratio (p x : ℝ) (n : ℕ) :
    ‖powerTerm p (n + 2) x‖ / ‖powerTerm p (n + 1) x‖ =
      |x| / |coefficient p (n + 1) / coefficient p (n + 2)| := by
  by_cases hx : x = 0
  · subst x
    simp [powerTerm]
  · have hax : |x| ≠ 0 := abs_ne_zero.mpr hx
    have hc1 : coefficient p (n + 1) ≠ 0 := coefficient_ne p _
    have hc2 : coefficient p (n + 2) ≠ 0 := coefficient_ne p _
    have hac1 : |coefficient p (n + 1)| ≠ 0 := abs_ne_zero.mpr hc1
    have hac2 : |coefficient p (n + 2)| ≠ 0 := abs_ne_zero.mpr hc2
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    simp only [powerTerm, abs_mul, abs_pow, abs_div]
    field_simp [hax, hac1, hac2, pow_ne_zero]
    ring

theorem gap1 :
    ∀ p : ℝ,
      (fun n : ℕ => |coefficient p (n + 1) / coefficient p (n + 2)|) =
        fun n : ℕ => radiusRatio p (n + 1) := by
  intro p
  funext n
  rw [abs_div, coefficient_abs, coefficient_abs]
  calc
    Real.rpow (base (n + 1)) p / Real.rpow (base (n + 2)) p =
        Real.rpow (base (n + 1) / base (n + 2)) p :=
      (Real.div_rpow (base_pos _).le (base_pos _).le p).symm
    _ = radiusRatio p (n + 1) := by
      rw [base_ratio]
      unfold radiusRatio
      congr 1 <;> push_cast <;> ring

theorem gap2 :
    ∀ p : ℝ, Tendsto (radiusRatio p) atTop (𝓝 (radius p)) := by
  intro p
  have hn : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    (tendsto_add_atTop_iff_nat 1).2 tendsto_id
  have hc :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hinv :
      Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp hc
  have hbase :
      Tendsto
        (fun n : ℕ => (((2 * n + 3 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)))
        atTop (𝓝 2) := by
    have heq :
        (fun n : ℕ => (((2 * n + 3 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) =
          fun n : ℕ => 2 + 1 / (((n + 1 : ℕ) : ℝ)) := by
      funext n
      have h : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp [h]
      push_cast
      ring
    rw [heq]
    convert tendsto_const_nhds.add hinv using 1 <;> norm_num
  unfold radiusRatio radius
  simpa [Nat.cast_add, Nat.cast_one] using
    hbase.rpow_const (p := p) (Or.inl (by norm_num : (2 : ℝ) ≠ 0))

theorem gap3 :
    ∀ p : ℝ,
      Tendsto
        (fun n : ℕ => |coefficient p (n + 1) / coefficient p (n + 2)|)
        atTop (𝓝 (radius p)) := by
  intro p
  rw [gap1 p]
  exact (tendsto_add_atTop_iff_nat 1).2 (gap2 p)

private theorem powerTerm_ratio_tendsto (p x : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ‖powerTerm p (n + 2) x‖ / ‖powerTerm p (n + 1) x‖)
      atTop (𝓝 (|x| / radius p)) := by
  have hrel :
      (fun n : ℕ =>
        ‖powerTerm p (n + 2) x‖ / ‖powerTerm p (n + 1) x‖) =
        fun n : ℕ => |x| / |coefficient p (n + 1) / coefficient p (n + 2)| := by
    funext n
    exact powerTerm_ratio p x n
  rw [hrel]
  exact tendsto_const_nhds.div (gap3 p)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) p).ne'

theorem gap4 :
    ∀ p : ℝ, HasConvergenceRadius p := by
  intro p
  constructor
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      simp [SeriesConvergesAt, powerTerm]
    · unfold SeriesConvergesAt
      apply summable_of_ratio_test_tendsto_lt_one
        ((div_lt_one (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) p)).2 hx)
      · exact Filter.Eventually.of_forall (fun n =>
          mul_ne_zero (coefficient_ne p _) (pow_ne_zero _ hx0))
      · simpa [Nat.add_assoc] using powerTerm_ratio_tendsto p x
  · intro x hx
    unfold SeriesConvergesAt
    apply not_summable_of_ratio_test_tendsto_gt_one
      ((one_lt_div (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) p)).2 hx)
    simpa [Nat.add_assoc] using powerTerm_ratio_tendsto p x

theorem gap5 :
    ∀ (p x : ℝ), x ∈ Set.Ioo (-(radius p)) (radius p) →
      SeriesConvergesAt p x := by
  intro p x hx
  exact (gap4 p).1 x (abs_lt.mpr hx)

theorem gap6 :
    ∀ p : ℝ,
      (fun n : ℕ => powerTerm p (n + 1) (-(radius p))) =
        fun n : ℕ => endpointMagnitude p (n + 1) := by
  intro p
  funext n
  let m := n + 1
  have hrpow : (radius p) ^ m = ((2 : ℝ) ^ m) ^ p := by
    exact Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) p m
  have hsign : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  change
    (-1 : ℝ) ^ m * Real.rpow (base m) p * (-(radius p)) ^ m =
      endpointMagnitude p m
  have hneg : (-(radius p)) ^ m = (-1 : ℝ) ^ m * (radius p) ^ m :=
    neg_pow _ _
  rw [hneg, hrpow]
  calc
    (-1 : ℝ) ^ m * Real.rpow (base m) p *
        ((-1 : ℝ) ^ m * ((2 : ℝ) ^ m) ^ p) =
        ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) *
          (Real.rpow (base m) p * ((2 : ℝ) ^ m) ^ p) := by ring
    _ = Real.rpow (base m) p * ((2 : ℝ) ^ m) ^ p := by rw [hsign, one_mul]
    _ = Real.rpow (base m * (2 : ℝ) ^ m) p :=
      (Real.mul_rpow (base_pos m).le (pow_nonneg (by norm_num) m)).symm
    _ = endpointMagnitude p m := by rw [← endpointBase_eq]; rfl

theorem gap7 :
    ∀ (p : ℝ) (n : ℕ),
      endpointMagnitude p n / endpointMagnitude p (n + 1) =
        endpointRatio p n := by
  intro p n
  rw [endpointMagnitude_eq, endpointMagnitude_eq]
  calc
    Real.rpow (endpointBase n) p / Real.rpow (endpointBase (n + 1)) p =
        Real.rpow (endpointBase n / endpointBase (n + 1)) p :=
      (Real.div_rpow (endpointBase_pos n).le (endpointBase_pos (n + 1)).le p).symm
    _ = endpointRatio p n := by rw [endpointBase_ratio]; rfl

theorem gap8 :
    ∀ (p : ℝ) (n : ℕ),
      endpointRatio p n =
        Real.rpow (1 + 1 / ((2 * n + 2 : ℕ) : ℝ)) p := by
  intro p n
  unfold endpointRatio
  congr 1
  have h : (((2 * n + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [h]
  push_cast
  ring

private theorem tendsto_raabe_expression (p : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ) *
          (Real.rpow (1 + 1 / ((2 * (n + 1) + 2 : ℕ) : ℝ)) p - 1))
      atTop (𝓝 (p / 2)) := by
  let t : ℕ → ℝ :=
    fun n => 1 / ((2 * (n + 1) + 2 : ℕ) : ℝ)
  have hdenNat :
      Tendsto (fun n : ℕ => 2 * (n + 1) + 2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hden :
      Tendsto (fun n : ℕ => (((2 * (n + 1) + 2 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdenNat
  have ht0 : Tendsto t atTop (𝓝 0) := by
    simpa [t, one_div] using tendsto_inv_atTop_zero.comp hden
  have ht : Tendsto t atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨ht0, ?_⟩
    exact Filter.Eventually.of_forall (fun n => by simp [t]; positivity)
  have hslope :=
    (Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := p)
      (Or.inl one_ne_zero)).tendsto_slope_zero_right.comp ht
  have hA :
      Tendsto
        (fun n : ℕ =>
          (t n)⁻¹ * (Real.rpow (1 + t n) p - 1))
        atTop (𝓝 p) := by
    simpa [smul_eq_mul] using hslope
  have hratio :
      Tendsto
        (fun n : ℕ =>
          (((n + 1 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ) + 1))
        atTop (𝓝 1) := by
    convert
      (tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1).comp
        (tendsto_add_atTop_nat 1) using 1
  have hB :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) * t n)
        atTop (𝓝 (1 / 2 : ℝ)) := by
    have hmul := (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul hratio
    convert hmul using 1
    · funext n
      dsimp [t]
      have hne : (((n + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
      field_simp [hne]
      push_cast
      ring
    · norm_num
  have hprod := hA.mul hB
  convert hprod using 1
  · funext n
    dsimp [t]
    have htne : (1 / (((2 * (n + 1) + 2 : ℕ) : ℝ)) : ℝ) ≠ 0 := by
      positivity
    field_simp [htne]
  · ring

theorem gap9 :
    ∀ p : ℝ,
      Tendsto (fun n : ℕ => raabeSeq p (n + 1)) atTop (𝓝 (p / 2)) := by
  intro p
  have h := tendsto_raabe_expression p
  convert h using 1
  funext n
  unfold raabeSeq
  rw [gap7, gap8]

theorem gap10 :
    ∀ p : ℝ,
      Tendsto
        (fun n : ℕ =>
          ((n + 1 : ℕ) : ℝ) *
            (Real.rpow (1 + 1 / ((2 * (n + 1) + 2 : ℕ) : ℝ)) p - 1))
        atTop (𝓝 (p / 2)) := by
  exact tendsto_raabe_expression

theorem gap11 :
    ∀ p : ℝ,
      Tendsto (fun n : ℕ => raabeSeq p (n + 1)) atTop (𝓝 (p / 2)) := by
  exact gap9

theorem gap12 :
    ∀ p : ℝ, 2 < p →
      Summable (fun n : ℕ => endpointMagnitude p (n + 1)) := by
  intro p hp
  exact summable_of_isBigO_nat
    ((asymptoticModel_summable_iff p).2 hp)
    (endpointMagnitude_isEquivalent p).isBigO

theorem gap13 :
    ∀ p : ℝ, 2 < p →
      Summable (fun n : ℕ =>
        |powerTerm p (n + 1) (-(radius p))|) := by
  intro p hp
  have heq :
      (fun n : ℕ => |powerTerm p (n + 1) (-(radius p))|) =
        fun n : ℕ => endpointMagnitude p (n + 1) := by
    funext n
    rw [congrFun (gap6 p) n, abs_of_pos (endpointMagnitude_pos p _)]
  rw [heq]
  exact gap12 p hp

theorem gap14 :
    ∀ p : ℝ, p ≤ 2 →
      ¬ Summable (fun n : ℕ => endpointMagnitude p (n + 1)) := by
  intro p hp hsum
  have hmodel :
      Summable (fun n : ℕ => asymptoticModel p (n + 1)) :=
    summable_of_isBigO_nat hsum
      (endpointMagnitude_isEquivalent p).symm.isBigO
  have := (asymptoticModel_summable_iff p).1 hmodel
  linarith

theorem gap15 :
    ∀ p : ℝ,
      (fun n : ℕ => powerTerm p (n + 1) (radius p)) =
        fun n : ℕ => (-1 : ℝ) ^ (n + 1) * endpointMagnitude p (n + 1) := by
  intro p
  funext n
  let m := n + 1
  have hrpow : (radius p) ^ m = ((2 : ℝ) ^ m) ^ p := by
    exact Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) p m
  change
    (-1 : ℝ) ^ m * Real.rpow (base m) p * (radius p) ^ m =
      (-1 : ℝ) ^ m * endpointMagnitude p m
  rw [hrpow, mul_assoc]
  calc
    (-1 : ℝ) ^ m *
        (Real.rpow (base m) p * ((2 : ℝ) ^ m) ^ p) =
        (-1 : ℝ) ^ m * Real.rpow (base m * (2 : ℝ) ^ m) p := by
      exact congrArg (fun z : ℝ => (-1 : ℝ) ^ m * z)
        (Real.mul_rpow (z := p) (base_pos m).le
          (pow_nonneg (by norm_num) m)).symm
    _ = (-1 : ℝ) ^ m * endpointMagnitude p m := by
      rw [← endpointBase_eq]
      rfl

theorem gap16 :
    ∀ p : ℝ, 2 < p →
      Summable (fun n : ℕ =>
        |powerTerm p (n + 1) (radius p)|) := by
  intro p hp
  have heq :
      (fun n : ℕ => |powerTerm p (n + 1) (radius p)|) =
        fun n : ℕ => endpointMagnitude p (n + 1) := by
    funext n
    rw [congrFun (gap15 p) n, abs_mul,
      abs_of_pos (endpointMagnitude_pos p _)]
    simp
  rw [heq]
  exact gap12 p hp

theorem gap17 :
    ∀ p : ℝ, 0 < p → p ≤ 2 →
      Tendsto
        (fun n : ℕ =>
          endpointMagnitude p (n + 1) / asymptoticModel p (n + 1))
        atTop (𝓝 1) := by
  intro p _ _
  exact endpointMagnitude_asymptotic p

theorem gap18 :
    ∀ p : ℝ, 0 < p →
      Tendsto (fun n : ℕ => endpointMagnitude p (n + 1))
        atTop (𝓝 0) := by
  intro p hp
  have hratio := endpointMagnitude_asymptotic p
  have hmodel := asymptoticModel_tendsto_zero p hp
  have hmul := hratio.mul hmodel
  convert hmul using 1
  · funext n
    have hm : 0 < asymptoticModel p (n + 1) := by
      unfold asymptoticModel
      apply Real.rpow_pos_of_pos
      exact div_pos Real.pi_pos (mul_pos (by norm_num) (by positivity))
    field_simp [hm.ne']
  · norm_num

theorem gap19 :
    ∀ (p : ℝ) (n : ℕ),
      endpointMagnitude p (n + 1) / endpointMagnitude p n =
        forwardEndpointRatio p n := by
  intro p n
  rw [endpointMagnitude_eq, endpointMagnitude_eq]
  calc
    Real.rpow (endpointBase (n + 1)) p / Real.rpow (endpointBase n) p =
        Real.rpow (endpointBase (n + 1) / endpointBase n) p :=
      (Real.div_rpow (endpointBase_pos (n + 1)).le (endpointBase_pos n).le p).symm
    _ = forwardEndpointRatio p n := by rw [endpointBase_forward_ratio]; rfl

theorem gap20 :
    ∀ (p : ℝ) (n : ℕ), 0 < p →
      forwardEndpointRatio p n < 1 := by
  intro p n hp
  unfold forwardEndpointRatio
  apply Real.rpow_lt_one
  · positivity
  · apply (div_lt_one (by positivity : (0 : ℝ) < ((2 * n + 3 : ℕ) : ℝ))).2
    push_cast
    linarith
  · exact hp

theorem gap21 :
    ∀ (p : ℝ) (n : ℕ), 0 < p →
      endpointMagnitude p (n + 1) / endpointMagnitude p n < 1 := by
  intro p n hp
  rw [gap19]
  exact gap20 p n hp

private theorem seriesConverges_iff_tendsto_sum_range (u : ℕ → ℝ) :
    ProofGap.SeriesConverges u ↔
      ∃ l : ℝ,
        Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, u n) atTop (𝓝 l) := by
  unfold ProofGap.SeriesConverges Summable HasSum
  rw [SummationFilter.conditional_filter_eq_map_range]
  simp only [tendsto_map'_iff]
  constructor <;> rintro ⟨l, hl⟩
  · exact ⟨l, by simpa [Function.comp_def] using hl⟩
  · exact ⟨l, by simpa [Function.comp_def] using hl⟩

private theorem seriesConverges_of_summable {u : ℕ → ℝ} (hu : Summable u) :
    ProofGap.SeriesConverges u := by
  unfold ProofGap.SeriesConverges
  exact hu.mono_filter (SummationFilter.conditional ℕ).le_atTop

private theorem seriesConverges_tendsto_zero {u : ℕ → ℝ}
    (hu : ProofGap.SeriesConverges u) : Tendsto u atTop (𝓝 0) := by
  obtain ⟨l, hl⟩ := (seriesConverges_iff_tendsto_sum_range u).1 hu
  have hshift := hl.comp (tendsto_add_atTop_nat 1)
  have hsub := hshift.sub hl
  convert hsub using 1
  · funext n
    simp [Function.comp_def, Finset.sum_range_succ]
  · ring

private theorem summable_of_seriesConverges_of_nonneg {u : ℕ → ℝ}
    (hu : ProofGap.SeriesConverges u) (hu0 : ∀ n, 0 ≤ u n) : Summable u := by
  obtain ⟨l, hl⟩ := (seriesConverges_iff_tendsto_sum_range u).1 hu
  exact ⟨l, (hasSum_iff_tendsto_nat_of_nonneg hu0 l).2 hl⟩

private theorem not_seriesConverges_of_ratio_test_tendsto_gt_one
    {u : ℕ → ℝ} {l : ℝ} (hl : 1 < l) (hu0 : ∀ n, u n ≠ 0)
    (h : Tendsto (fun n => ‖u (n + 1)‖ / ‖u n‖) atTop (𝓝 l)) :
    ¬ ProofGap.SeriesConverges u := by
  intro hu
  obtain ⟨r, hr1, hrl⟩ := exists_between hl
  have hge : ∀ᶠ n in atTop, r * ‖u n‖ ≤ ‖u (n + 1)‖ := by
    filter_upwards [h.eventually_const_le hrl] with n hn
    rwa [← le_div_iff₀ (norm_pos_iff.mpr (hu0 n))]
  rw [eventually_atTop] at hge
  obtain ⟨N, hN⟩ := hge
  have hgrowth : Tendsto (fun n : ℕ => ‖u (n + N)‖) atTop atTop := by
    apply tendsto_atTop_of_geom_le
      (v := fun n : ℕ => ‖u (n + N)‖) (c := r)
      (by simpa using norm_pos_iff.mpr (hu0 N)) hr1
    intro n
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hN (n + N) (by omega)
  have hzero : Tendsto (fun n : ℕ => ‖u (n + N)‖) atTop (𝓝 0) := by
    simpa using
      ((seriesConverges_tendsto_zero hu).comp (tendsto_add_atTop_nat N)).norm
  exact not_tendsto_atTop_of_tendsto_nhds hzero hgrowth

theorem gap22 :
    ∀ p : ℝ, 0 < p → p ≤ 2 →
      ConditionallySummable
        (fun n : ℕ => powerTerm p (n + 1) (radius p)) := by
  intro p hp hp2
  let a : ℕ → ℝ := fun n => endpointMagnitude p (n + 1)
  have ha0 : Tendsto a atTop (𝓝 0) := by
    exact gap18 p hp
  have haAnti : Antitone a := by
    apply antitone_nat_of_succ_le
    intro n
    exact (div_lt_one (endpointMagnitude_pos p (n + 1))).mp
      (gap21 p (n + 1) hp) |>.le
  let f : ℕ → ℝ := fun n => -a n
  have hfMono : Monotone f := by
    intro m n hmn
    exact neg_le_neg (haAnti hmn)
  have hf0 : Tendsto f atTop (𝓝 0) := by
    simpa [f] using ha0.neg
  obtain ⟨l, hl⟩ := hfMono.tendsto_alternating_series_of_tendsto_zero hf0
  have hconv : ProofGap.SeriesConverges
      (fun n : ℕ => powerTerm p (n + 1) (radius p)) := by
    apply (seriesConverges_iff_tendsto_sum_range _).2
    refine ⟨l, ?_⟩
    convert hl using 1
    funext N
    apply Finset.sum_congr rfl
    intro n hn
    rw [congrFun (gap15 p) n]
    simp [a, f, pow_succ]
  refine ⟨hconv, ?_⟩
  have habs :
      (fun n : ℕ => |powerTerm p (n + 1) (radius p)|) = a := by
    funext n
    rw [congrFun (gap15 p) n, abs_mul,
      abs_of_pos (endpointMagnitude_pos p _)]
    simp [a]
  rw [habs]
  exact gap14 p hp2

theorem gap23 :
    ¬ Summable (fun n : ℕ => (-1 : ℝ) ^ (n + 1)) := by
  intro hs
  have hzero :
      Tendsto (fun n : ℕ => ‖(-1 : ℝ) ^ (n + 1)‖) atTop (𝓝 (0 : ℝ)) := by
    simpa using hs.tendsto_atTop_zero.norm
  have hone :
      Tendsto (fun n : ℕ => ‖(-1 : ℝ) ^ (n + 1)‖) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have := tendsto_nhds_unique hone hzero
  norm_num at this

theorem gap24 :
    ∀ p : ℝ, p < 0 →
      ¬ Summable (fun n : ℕ => powerTerm p (n + 1) (radius p)) := by
  intro p hp hsum
  have hratio (n : ℕ) :
      1 < endpointMagnitude p (n + 1) / endpointMagnitude p n := by
    rw [gap19]
    unfold forwardEndpointRatio
    apply Real.one_lt_rpow_of_pos_of_lt_one_of_neg
    · positivity
    · apply (div_lt_one
        (by positivity : (0 : ℝ) < ((2 * n + 3 : ℕ) : ℝ))).2
      push_cast
      linarith
    · exact hp
  have hinc (n : ℕ) :
      endpointMagnitude p n < endpointMagnitude p (n + 1) :=
    (one_lt_div (endpointMagnitude_pos p n)).mp (hratio n)
  have hmono : StrictMono (endpointMagnitude p) :=
    strictMono_nat_of_lt_succ hinc
  have hnorm (n : ℕ) :
      ‖powerTerm p (n + 1) (radius p)‖ = endpointMagnitude p (n + 1) := by
    rw [Real.norm_eq_abs, congrFun (gap15 p) n, abs_mul,
      abs_of_pos (endpointMagnitude_pos p _)]
    simp
  have hzero :
      Tendsto (fun n : ℕ => endpointMagnitude p (n + 1)) atTop (𝓝 0) := by
    have hz :
        Tendsto (fun n : ℕ => ‖powerTerm p (n + 1) (radius p)‖)
          atTop (𝓝 (0 : ℝ)) := by
      simpa using hsum.tendsto_atTop_zero.norm
    convert hz using 1
    funext n
    exact (hnorm n).symm
  have hsmall := hzero.eventually
    (gt_mem_nhds (half_pos (endpointMagnitude_pos p 1)))
  rw [eventually_atTop] at hsmall
  obtain ⟨N, hN⟩ := hsmall
  have hu := hN N le_rfl
  have hl : endpointMagnitude p 1 ≤ endpointMagnitude p (N + 1) :=
    hmono.monotone (by omega)
  linarith [endpointMagnitude_pos p 1]

private theorem endpointMagnitude_monotone_of_nonpos (p : ℝ) (hp : p ≤ 0) :
    Monotone (endpointMagnitude p) := by
  apply monotone_nat_of_le_succ
  intro n
  have hratio : 1 ≤ forwardEndpointRatio p n := by
    unfold forwardEndpointRatio
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    · positivity
    · apply (div_le_one (by positivity : (0 : ℝ) < ((2 * n + 3 : ℕ) : ℝ))).2
      push_cast
      linarith
    · exact hp
  rw [← gap19] at hratio
  simpa only [one_mul] using
    (le_div_iff₀ (endpointMagnitude_pos p n)).mp hratio

private theorem endpointMagnitude_not_tendsto_zero_of_nonpos (p : ℝ) (hp : p ≤ 0) :
    ¬ Tendsto (fun n : ℕ => endpointMagnitude p (n + 1)) atTop (𝓝 0) := by
  intro hzero
  have hsmall := hzero.eventually
    (Iio_mem_nhds (half_pos (endpointMagnitude_pos p 1)))
  rw [eventually_atTop] at hsmall
  obtain ⟨N, hN⟩ := hsmall
  have hu := hN N le_rfl
  have hlower : endpointMagnitude p 1 ≤ endpointMagnitude p (N + 1) :=
    endpointMagnitude_monotone_of_nonpos p hp (by omega)
  linarith [endpointMagnitude_pos p 1]

theorem gap25 :
    ∀ (p x : ℝ),
      x ∈
          {y : ℝ |
            (2 < p ∧ -(radius p) ≤ y ∧ y ≤ radius p) ∨
            (0 < p ∧ p ≤ 2 ∧ -(radius p) < y ∧ y ≤ radius p) ∨
            (p ≤ 0 ∧ -(radius p) < y ∧ y < radius p)} ↔
        ProofGap.SeriesConverges (fun n : ℕ => powerTerm p (n + 1) x) := by
  intro p x
  have hradius : 0 < radius p :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) p
  constructor
  · rintro (⟨hp, hxl, hxu⟩ | ⟨hp, hp2, hxl, hxu⟩ | ⟨hp, hxl, hxu⟩)
    · by_cases hneg : x = -(radius p)
      · subst x
        apply seriesConverges_of_summable
        apply Summable.of_norm
        simpa [Real.norm_eq_abs] using gap13 p hp
      · by_cases hpos : x = radius p
        · subst x
          apply seriesConverges_of_summable
          apply Summable.of_norm
          simpa [Real.norm_eq_abs] using gap16 p hp
        · apply seriesConverges_of_summable
          exact gap5 p x ⟨lt_of_le_of_ne hxl (Ne.symm hneg),
            lt_of_le_of_ne hxu hpos⟩
    · by_cases hpos : x = radius p
      · subst x
        exact (gap22 p hp hp2).1
      · apply seriesConverges_of_summable
        exact gap5 p x ⟨hxl, lt_of_le_of_ne hxu hpos⟩
    · apply seriesConverges_of_summable
      exact gap5 p x ⟨hxl, hxu⟩
  · intro hconv
    have habs : |x| ≤ radius p := by
      by_contra hnot
      have houtside : radius p < |x| := lt_of_not_ge hnot
      have hx0 : x ≠ 0 := by
        intro hx
        subst x
        simp only [abs_zero] at houtside
        linarith
      have hne : ∀ n : ℕ, powerTerm p (n + 1) x ≠ 0 := by
        intro n
        exact mul_ne_zero (coefficient_ne p _) (pow_ne_zero _ hx0)
      have hratio : Tendsto
          (fun n : ℕ =>
            ‖powerTerm p (n + 1 + 1) x‖ / ‖powerTerm p (n + 1) x‖)
          atTop (𝓝 (|x| / radius p)) := by
        simpa [Nat.add_assoc] using powerTerm_ratio_tendsto p x
      exact (not_seriesConverges_of_ratio_test_tendsto_gt_one
        ((one_lt_div hradius).2 houtside) hne hratio) hconv
    have hbounds : -(radius p) ≤ x ∧ x ≤ radius p := abs_le.mp habs
    by_cases hp2 : 2 < p
    · exact Or.inl ⟨hp2, hbounds⟩
    · have hp_le_two : p ≤ 2 := le_of_not_gt hp2
      have hneg : x ≠ -(radius p) := by
        intro hx
        subst x
        have hendpoint : ProofGap.SeriesConverges
            (fun n : ℕ => endpointMagnitude p (n + 1)) :=
          hconv.congr (fun n => congrFun (gap6 p) n)
        exact gap14 p hp_le_two
          (summable_of_seriesConverges_of_nonneg hendpoint
            (fun n => (endpointMagnitude_pos p _).le))
      by_cases hp0 : 0 < p
      · exact Or.inr (Or.inl ⟨hp0, hp_le_two,
          lt_of_le_of_ne hbounds.1 (Ne.symm hneg), hbounds.2⟩)
      · have hp_nonpos : p ≤ 0 := le_of_not_gt hp0
        have hpos : x ≠ radius p := by
          intro hx
          subst x
          have htermZero := seriesConverges_tendsto_zero hconv
          have hmagZero : Tendsto
              (fun n : ℕ => endpointMagnitude p (n + 1)) atTop (𝓝 0) := by
            have hnorm : Tendsto
                (fun n : ℕ => ‖powerTerm p (n + 1) (radius p)‖)
                atTop (𝓝 0) := by
              simpa using htermZero.norm
            convert hnorm using 1
            funext n
            rw [Real.norm_eq_abs, congrFun (gap15 p) n, abs_mul,
              abs_of_pos (endpointMagnitude_pos p _)]
            simp
          exact endpointMagnitude_not_tendsto_zero_of_nonpos p hp_nonpos hmagZero
        exact Or.inr (Or.inr ⟨hp_nonpos,
          lt_of_le_of_ne hbounds.1 (Ne.symm hneg),
          lt_of_le_of_ne hbounds.2 hpos⟩)

end

end ProofGap.Exercise2819
