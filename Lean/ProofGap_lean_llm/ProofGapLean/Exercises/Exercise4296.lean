import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4296

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Point := ℝ × ℝ

def radius (p : Point) : ℝ :=
  Real.sqrt (p.1 ^ 2 + p.2 ^ 2)

def InDomain (p : Point) : Prop :=
  0 < p.1 + radius p

def P (p : Point) : ℝ :=
  radius p

def Q (p : Point) : ℝ :=
  p.1 * p.2 ^ 2 + p.2 * Real.log (p.1 + radius p)

def curl (p : Point) : ℝ :=
  deriv (fun x => Q (x, p.2)) p.1 -
    deriv (fun y => P (p.1, y)) p.2

def lineIntegral (γ : ℝ → Point) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    P (γ t) * deriv (fun s => (γ s).1) t +
      Q (γ t) * deriv (fun s => (γ s).2) t

def areaIntegral (S : Set Point) : ℝ :=
  ∫ p in S, p.2 ^ 2

def GreenAdmissible (S : Set Point) (γ : ℝ → Point) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = γ 1 ∧
    γ '' Set.Icc (0 : ℝ) 1 = frontier S ∧
      (∀ p ∈ S, InDomain p) ∧
        0 ≤ ∫ t in (0 : ℝ)..1,
          (γ t).1 * deriv (fun s => (γ s).2) t -
            (γ t).2 * deriv (fun s => (γ s).1) t

private theorem domain_sq_pos (p : Point) (hp : InDomain p) :
    0 < p.1 ^ 2 + p.2 ^ 2 := by
  have hnonneg :
      0 ≤ p.1 ^ 2 + p.2 ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  by_contra hn
  have hz : p.1 ^ 2 + p.2 ^ 2 = 0 := by
    linarith
  have hx : p.1 = 0 := by
    nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  have hy : p.2 = 0 := by
    nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  simp [InDomain, radius, hx, hy] at hp

private theorem radius_sq (p : Point)
    (hp : 0 ≤ p.1 ^ 2 + p.2 ^ 2) :
    radius p ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  exact Real.sq_sqrt hp

private theorem hasDerivAt_radius_x
    (p : Point) (hp : InDomain p) :
    HasDerivAt (fun x => radius (x, p.2))
      (p.1 / radius p) p.1 := by
  have hD : 0 < p.1 ^ 2 + p.2 ^ 2 :=
    domain_sq_pos p hp
  have hD0 : p.1 ^ 2 + p.2 ^ 2 ≠ 0 := ne_of_gt hD
  have hr0 : radius p ≠ 0 := by
    unfold radius
    exact ne_of_gt (Real.sqrt_pos.2 hD)
  have hinner :=
    ((hasDerivAt_id p.1).pow 2).add_const (p.2 ^ 2)
  have hroot :=
    (Real.hasDerivAt_sqrt hD0).comp p.1 hinner
  simpa [radius, Function.comp_def, div_eq_mul_inv,
    mul_assoc, mul_comm] using hroot

private theorem hasDerivAt_radius_y
    (p : Point) (hp : InDomain p) :
    HasDerivAt (fun y => radius (p.1, y))
      (p.2 / radius p) p.2 := by
  have hD : 0 < p.1 ^ 2 + p.2 ^ 2 :=
    domain_sq_pos p hp
  have hD0 : p.1 ^ 2 + p.2 ^ 2 ≠ 0 := ne_of_gt hD
  have hr0 : radius p ≠ 0 := by
    unfold radius
    exact ne_of_gt (Real.sqrt_pos.2 hD)
  have hinner :=
    (hasDerivAt_const p.2 (p.1 ^ 2)).add
      ((hasDerivAt_id p.2).pow 2)
  have hroot :=
    (Real.hasDerivAt_sqrt hD0).comp p.2 hinner
  simpa [radius, Function.comp_def, div_eq_mul_inv,
    mul_assoc, mul_comm, add_comm] using hroot

private theorem hasDerivAt_Q_x
    (p : Point) (hp : InDomain p) :
    HasDerivAt (fun x => Q (x, p.2))
      (p.2 ^ 2 + p.2 / radius p) p.1 := by
  have hsum :
      HasDerivAt (fun x => x + radius (x, p.2))
        (1 + p.1 / radius p) p.1 :=
    (hasDerivAt_id p.1).add (hasDerivAt_radius_x p hp)
  have hlog :=
    (Real.hasDerivAt_log (ne_of_gt hp)).comp p.1 hsum
  have hraw :=
    ((hasDerivAt_id p.1).mul_const (p.2 ^ 2)).add
      (hlog.const_mul p.2)
  convert hraw using 1
  have hD : 0 < p.1 ^ 2 + p.2 ^ 2 :=
    domain_sq_pos p hp
  have hr0 : radius p ≠ 0 := by
    unfold radius
    exact ne_of_gt (Real.sqrt_pos.2 hD)
  have hsum0 : p.1 + radius p ≠ 0 := ne_of_gt hp
  field_simp [hr0, hsum0]
  ring

private theorem curl_eq_on_domain
    (p : Point) (hp : InDomain p) :
    curl p = p.2 ^ 2 := by
  unfold curl
  have hyder :
      deriv (fun y => P (p.1, y)) p.2 =
        p.2 / radius p := by
    simpa [P] using (hasDerivAt_radius_y p hp).deriv
  rw [(hasDerivAt_Q_x p hp).deriv, hyder]
  ring

private theorem not_domain_y_zero (p : Point)
    (hp : ¬ InDomain p) : p.2 = 0 := by
  have hrad_nonneg : 0 ≤ radius p := Real.sqrt_nonneg _
  have hsq_nonneg :
      0 ≤ p.1 ^ 2 + p.2 ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hrsq := radius_sq p hsq_nonneg
  have hsum_nonneg : 0 ≤ p.1 + radius p := by
    have hsqrt_ge_abs :
        |p.1| ≤ radius p := by
      rw [← sq_le_sq₀ (abs_nonneg p.1) hrad_nonneg]
      rw [sq_abs, hrsq]
      exact le_add_of_nonneg_right (sq_nonneg p.2)
    rcases le_total 0 p.1 with hx | hx
    · linarith
    · rw [abs_of_nonpos hx] at hsqrt_ge_abs
      linarith
  have hsum : p.1 + radius p = 0 := by
    unfold InDomain at hp
    linarith
  have hrad : radius p = -p.1 := by linarith
  nlinarith

private theorem curl_eq_off_domain
    (p : Point) (hp : ¬ InDomain p) :
    curl p = p.2 ^ 2 := by
  rcases p with ⟨x, y⟩
  have hy : y = 0 := not_domain_y_zero (x, y) hp
  subst y
  have hQzero :
      (fun u => Q (u, (0 : ℝ))) =
        fun _u : ℝ => (0 : ℝ) := by
    funext u
    simp [Q]
  have hqx :
      deriv (fun u => Q (u, (0 : ℝ))) x = 0 := by
    rw [hQzero]
    simp
  by_cases hx : x = 0
  · subst hx
    have hPabs :
        (fun y => P ((0 : ℝ), y)) =
          fun y : ℝ => |y| := by
      funext y
      simp [P, radius, Real.sqrt_sq_eq_abs]
    have hpy :
        deriv (fun y => P ((0 : ℝ), y)) 0 = 0 := by
      rw [hPabs]
      exact deriv_abs_zero
    unfold curl
    rw [hqx, hpy]
    norm_num
  · have hD0 : x ^ 2 + 0 ^ 2 ≠ 0 := by
      simp [hx]
    have hinner :=
      (hasDerivAt_const (0 : ℝ) (x ^ 2)).add
        ((hasDerivAt_id (0 : ℝ)).pow 2)
    have hroot :=
      (Real.hasDerivAt_sqrt hD0).comp (0 : ℝ) hinner
    have hz :
        HasDerivAt
          (fun y => Real.sqrt (x ^ 2 + y ^ 2))
          0 0 := by
      convert hroot using 1 <;> simp
    have hpy :
        deriv (fun y => P (x, y)) 0 = 0 := by
      simpa [P, radius] using hz.deriv
    unfold curl
    rw [hqx, hpy]
    norm_num

private theorem curl_eq_sq_all (p : Point) :
    curl p = p.2 ^ 2 := by
  by_cases hp : InDomain p
  · exact curl_eq_on_domain p hp
  · exact curl_eq_off_domain p hp

theorem gap1 (p : Point) (hp : InDomain p) :
    curl p = p.2 ^ 2 + p.2 / radius p - p.2 / radius p := by
  rw [curl_eq_on_domain p hp]
  ring

theorem gap2 (p : Point) (hp : InDomain p) :
    p.2 ^ 2 + p.2 / radius p - p.2 / radius p = p.2 ^ 2 := by
  ring

theorem gap3 (p : Point) (hp : InDomain p) :
    curl p = p.2 ^ 2 := by
  exact curl_eq_on_domain p hp

theorem gap4 (S : Set Point) (γ : ℝ → Point)
    (hGreen : GreenAdmissible S γ)
    (hGreenTheorem : lineIntegral γ = ∫ p in S, curl p) :
    lineIntegral γ = areaIntegral S := by
  rw [hGreenTheorem]
  unfold areaIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall curl_eq_sq_all

end

end ProofGap.Exercise4296
