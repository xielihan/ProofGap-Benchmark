import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise2406
noncomputable section

open scoped Interval

variable (A B C : ℝ)

def D : ℝ := A * C - B ^ 2
def radicand (x : ℝ) : ℝ := C - D A B C * x ^ 2
def y₁ (x : ℝ) : ℝ := (-B * x - Real.sqrt (radicand A B C x)) / C
def y₂ (x : ℝ) : ℝ := (-B * x + Real.sqrt (radicand A B C x)) / C
def a : ℝ := Real.sqrt (C / D A B C)
def S : ℝ := ∫ x in (-a A B C)..(a A B C), y₂ A B C x - y₁ A B C x

theorem gap1 (x : ℝ) :
    y₁ A B C x =
      (-B * x - Real.sqrt (B ^ 2 * x ^ 2 - C * (A * x ^ 2 - 1))) / C := by
  unfold y₁ radicand
  have h :
      C - D A B C * x ^ 2 =
        B ^ 2 * x ^ 2 - C * (A * x ^ 2 - 1) := by
    unfold D
    ring
  rw [h]

theorem gap2 (x : ℝ) :
    y₂ A B C x =
      (-B * x + Real.sqrt (B ^ 2 * x ^ 2 - C * (A * x ^ 2 - 1))) / C := by
  unfold y₂ radicand
  have h :
      C - D A B C * x ^ 2 =
        B ^ 2 * x ^ 2 - C * (A * x ^ 2 - 1) := by
    unfold D
    ring
  rw [h]

theorem gap3 (hC : 0 < C) (hD : 0 < D A B C) (x : ℝ)
    (hx : 0 ≤ B ^ 2 * x ^ 2 - C * (A * x ^ 2 - 1)) :
    |x| ≤ a A B C := by
  have hrad :
      B ^ 2 * x ^ 2 - C * (A * x ^ 2 - 1) =
        C - D A B C * x ^ 2 := by
    unfold D
    ring
  rw [hrad] at hx
  have hratio : 0 ≤ C / D A B C := div_nonneg hC.le hD.le
  have ha_sq : (a A B C) ^ 2 = C / D A B C := by
    unfold a
    exact Real.sq_sqrt hratio
  have hscaled : D A B C * (a A B C) ^ 2 = C := by
    rw [ha_sq]
    field_simp [ne_of_gt hD]
  have ha_nonneg : 0 ≤ a A B C := by
    unfold a
    exact Real.sqrt_nonneg _
  by_contra hxa
  have hlt : a A B C < |x| := lt_of_not_ge hxa
  have hsum : 0 < |x| + a A B C := by
    nlinarith [abs_nonneg x]
  have hprod :
      0 < (|x| - a A B C) * (|x| + a A B C) :=
    mul_pos (sub_pos.mpr hlt) hsum
  have hsq : (a A B C) ^ 2 < |x| ^ 2 := by
    nlinarith
  have hmul :
      D A B C * (a A B C) ^ 2 < D A B C * |x| ^ 2 :=
    mul_lt_mul_of_pos_left hsq hD
  rw [sq_abs] at hmul
  linarith

theorem gap4 :
    S A B C =
      ∫ x in (-a A B C)..(a A B C), y₂ A B C x - y₁ A B C x := by
  rfl

theorem gap5 (hC : 0 < C) :
    (∫ x in (-a A B C)..(a A B C), y₂ A B C x - y₁ A B C x) =
      (2 / C) * ∫ x in (-a A B C)..(a A B C),
        Real.sqrt (B ^ 2 * x ^ 2 - C * (A * x ^ 2 - 1)) := by
  have hfun :
      (fun x : ℝ => y₂ A B C x - y₁ A B C x) =
        (fun x : ℝ =>
          (2 / C) * Real.sqrt (B ^ 2 * x ^ 2 - C * (A * x ^ 2 - 1))) := by
    funext x
    rw [gap2 A B C x, gap1 A B C x]
    ring
  rw [hfun, intervalIntegral.integral_const_mul]

theorem gap6 :
    (2 / C) * ∫ x in (-a A B C)..(a A B C),
        Real.sqrt (B ^ 2 * x ^ 2 - C * (A * x ^ 2 - 1)) =
      (2 / C) * ∫ x in (-a A B C)..(a A B C),
        Real.sqrt (C - D A B C * x ^ 2) := by
  have hfun :
      (fun x : ℝ =>
        Real.sqrt (B ^ 2 * x ^ 2 - C * (A * x ^ 2 - 1))) =
      (fun x : ℝ => Real.sqrt (C - D A B C * x ^ 2)) := by
    funext x
    apply congrArg Real.sqrt
    unfold D
    ring
  rw [hfun]

theorem gap7 (hC : 0 < C) :
    S A B C =
      (2 / C) * ∫ x in (-a A B C)..(a A B C),
        Real.sqrt (C - D A B C * x ^ 2) := by
  calc
    S A B C =
        ∫ x in (-a A B C)..(a A B C), y₂ A B C x - y₁ A B C x :=
      gap4 A B C
    _ = (2 / C) * ∫ x in (-a A B C)..(a A B C),
          Real.sqrt (B ^ 2 * x ^ 2 - C * (A * x ^ 2 - 1)) :=
      gap5 A B C hC
    _ = (2 / C) * ∫ x in (-a A B C)..(a A B C),
          Real.sqrt (C - D A B C * x ^ 2) :=
      gap6 A B C

theorem gap8 (hC : 0 < C) (hD : 0 < D A B C) :
    S A B C =
      (2 / C) * Real.sqrt (D A B C) *
        ∫ x in (-a A B C)..(a A B C),
          Real.sqrt ((a A B C) ^ 2 - x ^ 2) := by
  have hratio : 0 ≤ C / D A B C := div_nonneg hC.le hD.le
  have ha_sq : (a A B C) ^ 2 = C / D A B C := by
    unfold a
    exact Real.sq_sqrt hratio
  have hfun :
      (fun x : ℝ => Real.sqrt (C - D A B C * x ^ 2)) =
      (fun x : ℝ =>
        Real.sqrt (D A B C) * Real.sqrt ((a A B C) ^ 2 - x ^ 2)) := by
    funext x
    have hfactor :
        C - D A B C * x ^ 2 =
          D A B C * ((a A B C) ^ 2 - x ^ 2) := by
      rw [ha_sq]
      field_simp [ne_of_gt hD] <;> ring
    rw [hfactor, Real.sqrt_mul hD.le]
  calc
    S A B C =
        (2 / C) * ∫ x in (-a A B C)..(a A B C),
          Real.sqrt (C - D A B C * x ^ 2) :=
      gap7 A B C hC
    _ = (2 / C) * Real.sqrt (D A B C) *
          ∫ x in (-a A B C)..(a A B C),
            Real.sqrt ((a A B C) ^ 2 - x ^ 2) := by
      rw [hfun, intervalIntegral.integral_const_mul]
      ring

theorem gap9 (hC : 0 < C) (hD : 0 < D A B C) :
    (∫ x in (-a A B C)..(a A B C),
      Real.sqrt ((a A B C) ^ 2 - x ^ 2)) =
        Real.pi / 2 * (a A B C) ^ 2 := by
  let r : ℝ := a A B C
  have hr : 0 ≤ r := by
    dsimp [r]
    exact Real.sqrt_nonneg _
  have hpi : -Real.pi / 2 ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hnegpi : -Real.pi / 2 = -(Real.pi / 2) := by
    ring
  have hg : Continuous (fun x : ℝ => Real.sqrt (r ^ 2 - x ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))
  have htrans : Continuous (fun t : ℝ =>
      (r * Real.cos t) * Real.sqrt (r ^ 2 - (r * Real.sin t) ^ 2)) := by
    exact (continuous_const.mul Real.continuous_cos).mul
      (hg.comp (continuous_const.mul Real.continuous_sin))
  let G : ℝ → ℝ := fun u =>
    ∫ x in (-r)..u, Real.sqrt (r ^ 2 - x ^ 2)
  have hG (u : ℝ) :
      HasDerivAt G (Real.sqrt (r ^ 2 - u ^ 2)) u := by
    dsimp [G]
    exact intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable (-r) u)
      hg.stronglyMeasurable.stronglyMeasurableAtFilter
      hg.continuousAt
  have hcomp (t : ℝ) :
      HasDerivAt (fun s : ℝ => G (r * Real.sin s))
        ((r * Real.cos t) *
          Real.sqrt (r ^ 2 - (r * Real.sin t) ^ 2)) t := by
    simpa [Function.comp_def, mul_comm] using
      (hG (r * Real.sin t)).comp t
        ((Real.hasDerivAt_sin t).const_mul r)
  have hftc :
      (∫ t in (-Real.pi / 2)..(Real.pi / 2),
        (r * Real.cos t) * Real.sqrt (r ^ 2 - (r * Real.sin t) ^ 2)) =
      G (r * Real.sin (Real.pi / 2)) -
        G (r * Real.sin (-Real.pi / 2)) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hcomp t)
      (htrans.intervalIntegrable _ _)
  have hright :
      G (r * Real.sin (Real.pi / 2)) =
        ∫ x in (-r)..r, Real.sqrt (r ^ 2 - x ^ 2) := by
    simp [G, Real.sin_pi_div_two]
  have hleft_endpoint : G (r * Real.sin (-Real.pi / 2)) = 0 := by
    rw [hnegpi, Real.sin_neg, Real.sin_pi_div_two]
    simp [G]
  have hsubst :
      (∫ t in (-Real.pi / 2)..(Real.pi / 2),
        (r * Real.cos t) * Real.sqrt (r ^ 2 - (r * Real.sin t) ^ 2)) =
      ∫ x in (-r)..r, Real.sqrt (r ^ 2 - x ^ 2) := by
    calc
      (∫ t in (-Real.pi / 2)..(Real.pi / 2),
        (r * Real.cos t) * Real.sqrt (r ^ 2 - (r * Real.sin t) ^ 2)) =
          G (r * Real.sin (Real.pi / 2)) -
            G (r * Real.sin (-Real.pi / 2)) := hftc
      _ = ∫ x in (-r)..r, Real.sqrt (r ^ 2 - x ^ 2) := by
        rw [hright, hleft_endpoint]
        ring
  have hleft :
      (∫ t in (-Real.pi / 2)..(Real.pi / 2),
        (r * Real.cos t) * Real.sqrt (r ^ 2 - (r * Real.sin t) ^ 2)) =
      ∫ t in (-Real.pi / 2)..(Real.pi / 2), r ^ 2 * Real.cos t ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      rw [← hnegpi]
      simpa [Set.uIcc_of_le hpi] using ht
    have hcos : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ht'
    have hid : r ^ 2 - (r * Real.sin t) ^ 2 = (r * Real.cos t) ^ 2 := by
      have htrig := Real.sin_sq_add_cos_sq t
      calc
        r ^ 2 - (r * Real.sin t) ^ 2 = r ^ 2 * (1 - Real.sin t ^ 2) := by ring
        _ = r ^ 2 * Real.cos t ^ 2 := by
          rw [show 1 - Real.sin t ^ 2 = Real.cos t ^ 2 by nlinarith]
        _ = (r * Real.cos t) ^ 2 := by ring
    change (r * Real.cos t) *
        Real.sqrt (r ^ 2 - (r * Real.sin t) ^ 2) =
      r ^ 2 * Real.cos t ^ 2
    rw [hid, Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hr hcos)]
    ring
  let F : ℝ → ℝ := fun t => r ^ 2 * (t / 2 + Real.sin (2 * t) / 4)
  have hanti (t : ℝ) : HasDerivAt F (r ^ 2 * Real.cos t ^ 2) t := by
    dsimp [F]
    convert
      ((((hasDerivAt_id t).div_const 2).add
        (((Real.hasDerivAt_sin (2 * t)).comp t
          ((hasDerivAt_id t).const_mul 2)).div_const 4)).const_mul (r ^ 2)) using 1
    rw [Real.cos_two_mul]
    ring
  have heval :
      (∫ t in (-Real.pi / 2)..(Real.pi / 2), r ^ 2 * Real.cos t ^ 2) =
        F (Real.pi / 2) - F (-Real.pi / 2) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hanti t)
      ((continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _)
  change (∫ x in (-r)..r, Real.sqrt (r ^ 2 - x ^ 2)) =
    Real.pi / 2 * r ^ 2
  calc
    (∫ x in (-r)..r, Real.sqrt (r ^ 2 - x ^ 2)) =
        ∫ t in (-Real.pi / 2)..(Real.pi / 2),
          (r * Real.cos t) * Real.sqrt (r ^ 2 - (r * Real.sin t) ^ 2) :=
      hsubst.symm
    _ = ∫ t in (-Real.pi / 2)..(Real.pi / 2), r ^ 2 * Real.cos t ^ 2 := hleft
    _ = F (Real.pi / 2) - F (-Real.pi / 2) := heval
    _ = Real.pi / 2 * r ^ 2 := by
      have hp : 2 * (Real.pi / 2) = Real.pi := by ring
      have hn : 2 * (-Real.pi / 2) = -Real.pi := by ring
      dsimp [F]
      rw [hp, hn, Real.sin_pi, Real.sin_neg, Real.sin_pi]
      ring

theorem gap10 (hC : 0 < C) (hD : 0 < D A B C) :
    (2 / C) * Real.sqrt (D A B C) *
        (Real.pi / 2 * (a A B C) ^ 2) =
      Real.pi / Real.sqrt (D A B C) := by
  have hratio : 0 ≤ C / D A B C := div_nonneg hC.le hD.le
  have ha_sq : (a A B C) ^ 2 = C / D A B C := by
    unfold a
    exact Real.sq_sqrt hratio
  have hs_pos : 0 < Real.sqrt (D A B C) := Real.sqrt_pos.2 hD
  have hs_sq : (Real.sqrt (D A B C)) ^ 2 = D A B C :=
    Real.sq_sqrt hD.le
  have ha_sq' :
      (a A B C) ^ 2 = C / (Real.sqrt (D A B C)) ^ 2 := by
    calc
      (a A B C) ^ 2 = C / D A B C := ha_sq
      _ = C / (Real.sqrt (D A B C)) ^ 2 := by rw [hs_sq]
  rw [ha_sq']
  field_simp [ne_of_gt hC, ne_of_gt hs_pos] <;> ring

theorem gap11 (hC : 0 < C) (hD : 0 < D A B C) :
    S A B C = Real.pi / Real.sqrt (D A B C) := by
  calc
    S A B C =
        (2 / C) * Real.sqrt (D A B C) *
          ∫ x in (-a A B C)..(a A B C),
            Real.sqrt ((a A B C) ^ 2 - x ^ 2) :=
      gap8 A B C hC hD
    _ = (2 / C) * Real.sqrt (D A B C) *
          (Real.pi / 2 * (a A B C) ^ 2) := by
      rw [gap9 A B C hC hD]
    _ = Real.pi / Real.sqrt (D A B C) :=
      gap10 A B C hC hD

end
end ProofGap.Exercise2406
