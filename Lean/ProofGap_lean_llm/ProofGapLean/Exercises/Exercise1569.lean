import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1569

noncomputable section

def height (R r : ℝ) : ℝ := Real.sqrt (R ^ 2 - r ^ 2)
def volume (R r : ℝ) : ℝ := 2 * Real.pi * r ^ 2 * height R r
def optimalRadius (R : ℝ) : ℝ := Real.sqrt (2 / 3) * R
def optimalHalfHeight (R : ℝ) : ℝ := R / Real.sqrt 3

def Feasible (R r h : ℝ) : Prop :=
  0 < r ∧ 0 < h ∧ r ^ 2 + h ^ 2 = R ^ 2

def IsOptimal (R r h : ℝ) : Prop :=
  Feasible R r h ∧ ∀ r₁ h₁, Feasible R r₁ h₁ →
    2 * Real.pi * r₁ ^ 2 * h₁ ≤ 2 * Real.pi * r ^ 2 * h

private theorem optimal_feasible (R : ℝ) (hR : 0 < R) :
    Feasible R (optimalRadius R) (optimalHalfHeight R) := by
  have hspos : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have htpos : 0 < Real.sqrt (2 / 3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hssq : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have htsq : Real.sqrt (2 / 3 : ℝ) ^ 2 = 2 / 3 :=
    Real.sq_sqrt (by norm_num)
  unfold Feasible optimalRadius optimalHalfHeight
  refine ⟨mul_pos htpos hR, div_pos hR hspos, ?_⟩
  calc
    (Real.sqrt (2 / 3 : ℝ) * R) ^ 2 + (R / Real.sqrt 3) ^ 2 =
        (2 / 3 : ℝ) * R ^ 2 + R ^ 2 / 3 := by
          rw [mul_pow, htsq, div_pow, hssq]
    _ = R ^ 2 := by ring

private theorem optimal_product_eq (R : ℝ) :
    (optimalRadius R) ^ 2 * optimalHalfHeight R =
      2 * R ^ 3 / (3 * Real.sqrt 3) := by
  have htsq : Real.sqrt (2 / 3 : ℝ) ^ 2 = 2 / 3 :=
    Real.sq_sqrt (by norm_num)
  unfold optimalRadius optimalHalfHeight
  rw [mul_pow, htsq]
  ring

private theorem feasible_product_difference (R r h : ℝ)
    (hfeas : Feasible R r h) :
    (h - R / Real.sqrt 3) ^ 2 * (h + 2 * (R / Real.sqrt 3)) =
      2 * R ^ 3 / (3 * Real.sqrt 3) - r ^ 2 * h := by
  rcases hfeas with ⟨hr, hh, heq⟩
  have hssq : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3 : Real.sqrt (3 : ℝ) ^ 3 = 3 * Real.sqrt 3 := by
    calc
      Real.sqrt (3 : ℝ) ^ 3 = Real.sqrt (3 : ℝ) ^ 2 * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [hssq]
  have hdivsq : (R / Real.sqrt 3) ^ 2 = R ^ 2 / 3 := by
    rw [div_pow, hssq]
  have hdivcube : (R / Real.sqrt 3) ^ 3 = R ^ 3 / (3 * Real.sqrt 3) := by
    rw [div_pow, hs3]
  have heqh : r ^ 2 * h + h ^ 3 = R ^ 2 * h := by
    calc
      r ^ 2 * h + h ^ 3 = (r ^ 2 + h ^ 2) * h := by ring
      _ = R ^ 2 * h := by rw [heq]
  calc
    (h - R / Real.sqrt 3) ^ 2 * (h + 2 * (R / Real.sqrt 3)) =
        h ^ 3 - 3 * (R / Real.sqrt 3) ^ 2 * h +
          2 * (R / Real.sqrt 3) ^ 3 := by ring
    _ = h ^ 3 - R ^ 2 * h + 2 * R ^ 3 / (3 * Real.sqrt 3) := by
      rw [hdivsq, hdivcube]
      ring
    _ = 2 * R ^ 3 / (3 * Real.sqrt 3) - r ^ 2 * h := by
      nlinarith

private theorem feasible_product_le (R r h : ℝ) (hR : 0 < R)
    (hfeas : Feasible R r h) :
    r ^ 2 * h ≤ 2 * R ^ 3 / (3 * Real.sqrt 3) := by
  have hdifference := feasible_product_difference R r h hfeas
  rcases hfeas with ⟨hr, hh, heq⟩
  have hspos : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hfactor : 0 ≤ h + 2 * (R / Real.sqrt 3) := by
    exact (add_pos hh (mul_pos (by norm_num) (div_pos hR hspos))).le
  have hnonneg :
      0 ≤ (h - R / Real.sqrt 3) ^ 2 * (h + 2 * (R / Real.sqrt 3)) :=
    mul_nonneg (sq_nonneg _) hfactor
  rw [hdifference] at hnonneg
  exact sub_nonneg.mp hnonneg

private theorem feasible_eq_optimal_of_ge (R r h : ℝ) (hR : 0 < R)
    (hfeas : Feasible R r h)
    (hge : (optimalRadius R) ^ 2 * optimalHalfHeight R ≤ r ^ 2 * h) :
    r = optimalRadius R ∧ h = optimalHalfHeight R := by
  have hdifference := feasible_product_difference R r h hfeas
  have hbound := feasible_product_le R r h hR hfeas
  have hoptimal := optimal_product_eq R
  have hproduct : r ^ 2 * h = 2 * R ^ 3 / (3 * Real.sqrt 3) := by
    nlinarith
  rcases hfeas with ⟨hr, hh, heq⟩
  have hspos : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hfactor_pos : 0 < h + 2 * (R / Real.sqrt 3) :=
    add_pos hh (mul_pos (by norm_num) (div_pos hR hspos))
  have hzero :
      (h - R / Real.sqrt 3) ^ 2 * (h + 2 * (R / Real.sqrt 3)) = 0 := by
    rw [hdifference, hproduct]
    ring
  have hsquare : (h - R / Real.sqrt 3) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hzero with hsquare | hfactor
    · exact hsquare
    · exact False.elim (hfactor_pos.ne' hfactor)
  have hhopt : h = optimalHalfHeight R := by
    unfold optimalHalfHeight
    nlinarith [sq_nonneg (h - R / Real.sqrt 3)]
  rcases optimal_feasible R hR with ⟨hropt, hhpos, heqopt⟩
  have hrsq : r ^ 2 = (optimalRadius R) ^ 2 := by
    rw [hhopt] at heq
    nlinarith
  have hreq : r = optimalRadius R := by
    nlinarith
  exact ⟨hreq, hhopt⟩

theorem gap1 (R r h : ℝ) (hfeas : Feasible R r h) :
    h = height R r := by
  rcases hfeas with ⟨hr, hh, heq⟩
  unfold height
  have hrad : 0 ≤ R ^ 2 - r ^ 2 := by
    nlinarith [sq_nonneg h]
  have hsqrt_sq := Real.sq_sqrt hrad
  have hsqrt_nonneg := Real.sqrt_nonneg (R ^ 2 - r ^ 2)
  nlinarith

theorem gap2 (R r : ℝ) :
    volume R r = 2 * Real.pi * r ^ 2 * Real.sqrt (R ^ 2 - r ^ 2) := by
  rfl

theorem gap3 (R r : ℝ) (hr : 0 < r) (hrad : 0 < R ^ 2 - r ^ 2) :
    deriv (volume R) r =
      2 * Real.pi * r * (2 * R ^ 2 - 3 * r ^ 2) /
        Real.sqrt (R ^ 2 - r ^ 2) := by
  have hsqrt_pos : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.2 hrad
  have hsqrt_sq : Real.sqrt (R ^ 2 - r ^ 2) ^ 2 = R ^ 2 - r ^ 2 :=
    Real.sq_sqrt hrad.le
  have hconstR : HasDerivAt (fun _ : ℝ => R ^ 2) 0 r :=
    hasDerivAt_const r (R ^ 2)
  have hinner0 := hconstR.sub ((hasDerivAt_id r).pow 2)
  have hinner : HasDerivAt
      (fun x : ℝ => R ^ 2 - x ^ 2) (-(2 * r)) r := by
    simpa [Pi.sub_apply, Pi.pow_apply] using hinner0
  have hsqrt : HasDerivAt
      (fun x : ℝ => Real.sqrt (R ^ 2 - x ^ 2))
      ((1 / (2 * Real.sqrt (R ^ 2 - r ^ 2))) * (-(2 * r))) r := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sqrt hrad.ne').comp r hinner
  have hconst : HasDerivAt (fun _ : ℝ => 2 * Real.pi) 0 r :=
    hasDerivAt_const r (2 * Real.pi)
  have hpoly : HasDerivAt
      (fun x : ℝ => 2 * Real.pi * x ^ 2)
      ((2 * Real.pi) * (2 * r)) r := by
    simpa [Pi.mul_apply, Pi.pow_apply] using
      hconst.mul ((hasDerivAt_id r).pow 2)
  have hv : HasDerivAt
      (fun x : ℝ => 2 * Real.pi * x ^ 2 * Real.sqrt (R ^ 2 - x ^ 2))
      (((2 * Real.pi) * (2 * r)) * Real.sqrt (R ^ 2 - r ^ 2) +
        (2 * Real.pi * r ^ 2) *
          ((1 / (2 * Real.sqrt (R ^ 2 - r ^ 2))) * (-(2 * r)))) r :=
    hpoly.mul hsqrt
  unfold volume height
  calc
    deriv (fun x : ℝ => 2 * Real.pi * x ^ 2 * Real.sqrt (R ^ 2 - x ^ 2)) r =
        ((2 * Real.pi) * (2 * r)) * Real.sqrt (R ^ 2 - r ^ 2) +
          (2 * Real.pi * r ^ 2) *
            ((1 / (2 * Real.sqrt (R ^ 2 - r ^ 2))) * (-(2 * r))) := hv.deriv
    _ = 2 * Real.pi * r *
          (2 * Real.sqrt (R ^ 2 - r ^ 2) ^ 2 - r ^ 2) /
            Real.sqrt (R ^ 2 - r ^ 2) := by
          field_simp [hsqrt_pos.ne'] <;> ring
    _ = 2 * Real.pi * r * (2 * R ^ 2 - 3 * r ^ 2) /
          Real.sqrt (R ^ 2 - r ^ 2) := by
          rw [hsqrt_sq]
          ring

theorem gap4 (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hrad : 0 < R ^ 2 - r ^ 2) (hcrit : deriv (volume R) r = 0) :
    r = optimalRadius R := by
  have hsqrt_pos : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.2 hrad
  have hformula := gap3 R r hr hrad
  have hzero :
      2 * Real.pi * r * (2 * R ^ 2 - 3 * r ^ 2) /
        Real.sqrt (R ^ 2 - r ^ 2) = 0 := by
    calc
      2 * Real.pi * r * (2 * R ^ 2 - 3 * r ^ 2) /
          Real.sqrt (R ^ 2 - r ^ 2) = deriv (volume R) r := hformula.symm
      _ = 0 := hcrit
  have hnumer : 2 * Real.pi * r * (2 * R ^ 2 - 3 * r ^ 2) = 0 := by
    rcases div_eq_zero_iff.mp hzero with hnumer | hden
    · exact hnumer
    · exact False.elim (hsqrt_pos.ne' hden)
  have hquad : 2 * R ^ 2 - 3 * r ^ 2 = 0 := by
    rcases mul_eq_zero.mp hnumer with hpir | hquad
    · rcases mul_eq_zero.mp hpir with hpi | hrzero
      · nlinarith [Real.pi_pos]
      · nlinarith
    · exact hquad
  have htpos : 0 < Real.sqrt (2 / 3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have htsq : Real.sqrt (2 / 3 : ℝ) ^ 2 = 2 / 3 :=
    Real.sq_sqrt (by norm_num)
  have hcandidate_pos : 0 < Real.sqrt (2 / 3 : ℝ) * R := mul_pos htpos hR
  have hsquares : r ^ 2 = (Real.sqrt (2 / 3 : ℝ) * R) ^ 2 := by
    rw [mul_pow, htsq]
    nlinarith
  unfold optimalRadius
  nlinarith

theorem gap5 (R r h : ℝ) (hR : 0 < R) (hopt : IsOptimal R r h) :
    r = optimalRadius R ∧ h = optimalHalfHeight R := by
  rcases hopt with ⟨hfeas, hmax⟩
  have hcanonical := optimal_feasible R hR
  have hvolume := hmax (optimalRadius R) (optimalHalfHeight R) hcanonical
  have hscale : 0 < (2 * Real.pi : ℝ) :=
    mul_pos (by norm_num) Real.pi_pos
  have hvolume' :
      (2 * Real.pi) * ((optimalRadius R) ^ 2 * optimalHalfHeight R) ≤
        (2 * Real.pi) * (r ^ 2 * h) := by
    simpa [mul_assoc] using hvolume
  have hge : (optimalRadius R) ^ 2 * optimalHalfHeight R ≤ r ^ 2 * h := by
    by_contra hnot
    have hlt : r ^ 2 * h < (optimalRadius R) ^ 2 * optimalHalfHeight R :=
      lt_of_not_ge hnot
    have hscaled_lt := mul_lt_mul_of_pos_left hlt hscale
    exact (not_lt_of_ge hvolume') hscaled_lt
  exact feasible_eq_optimal_of_ge R r h hR hfeas hge

theorem gap6 (R : ℝ) (hR : 0 < R) :
    ∀ r ∈ Set.Ioo 0 R, volume R r ≤ volume R (optimalRadius R) := by
  intro r hrange
  rcases hrange with ⟨hr, hrR⟩
  have hrad : 0 < R ^ 2 - r ^ 2 := by
    have hprod : 0 < (R - r) * (R + r) :=
      mul_pos (sub_pos.2 hrR) (add_pos hR hr)
    nlinarith
  have hheight_pos : 0 < height R r := by
    exact Real.sqrt_pos.2 hrad
  have hfeas : Feasible R r (height R r) := by
    refine ⟨hr, hheight_pos, ?_⟩
    unfold height
    have hsquare := Real.sq_sqrt hrad.le
    nlinarith
  have hbound := feasible_product_le R r (height R r) hR hfeas
  have hproduct :
      r ^ 2 * height R r ≤
        (optimalRadius R) ^ 2 * optimalHalfHeight R := by
    rw [optimal_product_eq R]
    exact hbound
  have hscale : 0 ≤ (2 * Real.pi : ℝ) :=
    (mul_pos (by norm_num) Real.pi_pos).le
  have hscaled :
      (2 * Real.pi) * (r ^ 2 * height R r) ≤
        (2 * Real.pi) * ((optimalRadius R) ^ 2 * optimalHalfHeight R) :=
    mul_le_mul_of_nonneg_left hproduct hscale
  have hcanonical_height := gap1 R (optimalRadius R) (optimalHalfHeight R)
    (optimal_feasible R hR)
  unfold volume
  rw [← hcanonical_height]
  simpa only [mul_assoc] using hscaled

theorem gap7 (R : ℝ) (hR : 0 < R) :
    volume R (optimalRadius R) =
      4 * Real.pi * R ^ 3 / (3 * Real.sqrt 3) := by
  have hcanonical_height := gap1 R (optimalRadius R) (optimalHalfHeight R)
    (optimal_feasible R hR)
  unfold volume
  rw [← hcanonical_height]
  calc
    2 * Real.pi * (optimalRadius R) ^ 2 * optimalHalfHeight R =
        2 * Real.pi * ((optimalRadius R) ^ 2 * optimalHalfHeight R) := by ring
    _ = 2 * Real.pi * (2 * R ^ 3 / (3 * Real.sqrt 3)) := by
      rw [optimal_product_eq R]
    _ = 4 * Real.pi * R ^ 3 / (3 * Real.sqrt 3) := by ring

theorem gap8 (R r h : ℝ) (hR : 0 < R) (hopt : IsOptimal R r h) :
    2 * Real.pi * r ^ 2 * h =
      4 * Real.pi * R ^ 3 / (3 * Real.sqrt 3) := by
  rcases gap5 R r h hR hopt with ⟨hr, hh⟩
  rw [hr, hh]
  calc
    2 * Real.pi * (optimalRadius R) ^ 2 * optimalHalfHeight R =
        2 * Real.pi * ((optimalRadius R) ^ 2 * optimalHalfHeight R) := by ring
    _ = 2 * Real.pi * (2 * R ^ 3 / (3 * Real.sqrt 3)) := by
      rw [optimal_product_eq R]
    _ = 4 * Real.pi * R ^ 3 / (3 * Real.sqrt 3) := by ring

theorem gap9 (R : ℝ) (hR : 0 < R) :
    IsOptimal R (optimalRadius R) (optimalHalfHeight R) := by
  refine ⟨optimal_feasible R hR, ?_⟩
  intro r₁ h₁ hfeas
  have hbound := feasible_product_le R r₁ h₁ hR hfeas
  have hproduct : r₁ ^ 2 * h₁ ≤
      (optimalRadius R) ^ 2 * optimalHalfHeight R := by
    rw [optimal_product_eq R]
    exact hbound
  have hscale : 0 ≤ (2 * Real.pi : ℝ) :=
    (mul_pos (by norm_num) Real.pi_pos).le
  have hscaled :
      (2 * Real.pi) * (r₁ ^ 2 * h₁) ≤
        (2 * Real.pi) * ((optimalRadius R) ^ 2 * optimalHalfHeight R) :=
    mul_le_mul_of_nonneg_left hproduct hscale
  simpa only [mul_assoc] using hscaled

theorem gap10 (R : ℝ) (hR : 0 < R) :
    (optimalRadius R, 2 * optimalHalfHeight R) =
      (Real.sqrt (2 / 3) * R, 2 * R / Real.sqrt 3) := by
  apply Prod.ext
  · rfl
  · unfold optimalHalfHeight
    ring

end

end ProofGap.Exercise1569
