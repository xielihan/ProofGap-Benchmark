import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1246

noncomputable section

def quadratic (a b c x : ℝ) : ℝ := a * x ^ 2 + b * x + c
def cubic (x : ℝ) : ℝ := x ^ 3
def recip (x : ℝ) : ℝ := 1 / x

private theorem deriv_recip_formula (x : ℝ) :
    deriv recip x = -(1 / x ^ 2) := by
  have hfun : recip = (fun y : ℝ => y⁻¹) := by
    funext y
    simp [ProofGap.Exercise1246.recip]
  rw [hfun]
  by_cases hx : x = 0
  · subst x
    simp
  · simpa [one_div, inv_pow] using ((hasDerivAt_id x).inv hx).deriv

theorem gap1 (a b c x : ℝ) :
    deriv (quadratic a b c) x = 2 * a * x + b := by
  have hsq : HasDerivAt (fun y : ℝ => y * y) (2 * x) x := by
    simpa [two_mul] using (hasDerivAt_id x).mul (hasDerivAt_id x)
  have hraw :=
    ((hsq.const_mul a).add ((hasDerivAt_id x).const_mul b)).add
      (hasDerivAt_const x c)
  have h : HasDerivAt (quadratic a b c) (2 * a * x + b) x := by
    convert hraw using 1
    · funext y
      change a * y ^ 2 + b * y + c = a * (y * y) + b * y + c
      ring
    · ring
  exact h.deriv

theorem gap2 (a b c x Δx θ : ℝ)
    (hinc : quadratic a b c (x + Δx) - quadratic a b c x =
      Δx * deriv (quadratic a b c) (x + θ * Δx)) :
    a * (x + Δx) ^ 2 + b * (x + Δx) + c -
        a * x ^ 2 - b * x - c =
      Δx * (2 * a * (x + θ * Δx) + b) := by
  rw [gap1] at hinc
  unfold quadratic at hinc
  nlinarith [hinc]

theorem gap3 (a b c x Δx θ : ℝ) (ha : a ≠ 0) (hΔ : Δx ≠ 0)
    (hinc : quadratic a b c (x + Δx) - quadratic a b c x =
      Δx * deriv (quadratic a b c) (x + θ * Δx)) :
    θ = 1 / 2 := by
  have h := gap2 a b c x Δx θ hinc
  have hp : a * Δx ^ 2 * (1 - 2 * θ) = 0 := by
    calc
      a * Δx ^ 2 * (1 - 2 * θ) =
          (a * (x + Δx) ^ 2 + b * (x + Δx) + c -
            a * x ^ 2 - b * x - c) -
            Δx * (2 * a * (x + θ * Δx) + b) := by ring
      _ = 0 := by rw [h]; ring
  have hne : a * Δx ^ 2 ≠ 0 :=
    mul_ne_zero ha (pow_ne_zero 2 hΔ)
  have hz : 1 - 2 * θ = 0 :=
    (mul_eq_zero.mp hp).resolve_left hne
  nlinarith

theorem gap4 (x : ℝ) :
    deriv cubic x = 3 * x ^ 2 := by
  have hsquare : HasDerivAt (fun y : ℝ => y * y) (2 * x) x := by
    simpa [two_mul] using (hasDerivAt_id x).mul (hasDerivAt_id x)
  have hcube := hsquare.mul (hasDerivAt_id x)
  have h : HasDerivAt cubic (3 * x ^ 2) x := by
    convert hcube using 1
    · funext y
      change y ^ 3 = (y * y) * y
      ring
    · simp only [id]
      ring
  exact h.deriv

theorem gap5 (x Δx θ : ℝ)
    (hinc : cubic (x + Δx) - cubic x =
      Δx * deriv cubic (x + θ * Δx)) :
    (x + Δx) ^ 3 - x ^ 3 = 3 * Δx * (x + θ * Δx) ^ 2 := by
  rw [gap4] at hinc
  unfold cubic at hinc
  nlinarith [hinc]

theorem gap6 (Δx θ : ℝ) (hΔ : Δx ≠ 0)
    (hinc : cubic Δx - cubic 0 = Δx * deriv cubic (θ * Δx)) :
    θ = Real.sqrt 3 / 3 ∨ θ = -Real.sqrt 3 / 3 := by
  have h : Δx ^ 3 = Δx * (3 * (θ * Δx) ^ 2) := by
    rw [gap4] at hinc
    simpa [cubic] using hinc
  have hp : Δx ^ 3 * (1 - 3 * θ ^ 2) = 0 := by
    calc
      Δx ^ 3 * (1 - 3 * θ ^ 2) =
          Δx ^ 3 - Δx * (3 * (θ * Δx) ^ 2) := by ring
      _ = 0 := by rw [h]; ring
  have hd3 : Δx ^ 3 ≠ 0 := pow_ne_zero 3 hΔ
  have hθ : 1 - 3 * θ ^ 2 = 0 :=
    (mul_eq_zero.mp hp).resolve_left hd3
  have hs : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hfactor :
      (θ - Real.sqrt 3 / 3) * (θ + Real.sqrt 3 / 3) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hpos | hneg
  · left
    nlinarith
  · right
    nlinarith

theorem gap7 (x Δx θ : ℝ) (hx : x ≠ 0) (hΔ : Δx ≠ 0)
    (hinc : cubic (x + Δx) - cubic x =
      Δx * deriv cubic (x + θ * Δx)) :
    3 * θ ^ 2 * Δx + 6 * θ * x - (3 * x + Δx) = 0 := by
  have h := gap5 x Δx θ hinc
  have hp :
      Δx ^ 2 * (3 * θ ^ 2 * Δx + 6 * θ * x - (3 * x + Δx)) = 0 := by
    calc
      Δx ^ 2 * (3 * θ ^ 2 * Δx + 6 * θ * x - (3 * x + Δx)) =
          3 * Δx * (x + θ * Δx) ^ 2 -
            ((x + Δx) ^ 3 - x ^ 3) := by ring
      _ = 0 := by rw [h]; ring
  exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero 2 hΔ)

theorem gap8 (x Δx θ : ℝ) (hx : x ≠ 0) (hΔ : Δx ≠ 0)
    (hinc : cubic (x + Δx) - cubic x =
      Δx * deriv cubic (x + θ * Δx)) :
    θ = (Real.sqrt (x ^ 2 + x * Δx + (1 / 3 : ℝ) * Δx ^ 2) - x) / Δx ∨
      θ = (-Real.sqrt (x ^ 2 + x * Δx + (1 / 3 : ℝ) * Δx ^ 2) - x) / Δx := by
  have hp := gap7 x Δx θ hx hΔ hinc
  have hmul := congrArg (fun z : ℝ => z * Δx) hp
  let s : ℝ := x ^ 2 + x * Δx + (1 / 3 : ℝ) * Δx ^ 2
  have hsquare : (θ * Δx + x) ^ 2 = s := by
    dsimp [s]
    nlinarith [hmul]
  have hsnonneg : 0 ≤ s := by
    rw [← hsquare]
    exact sq_nonneg (θ * Δx + x)
  have hsqrt : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hsnonneg
  have hfactor :
      (θ * Δx + x - Real.sqrt s) *
        (θ * Δx + x + Real.sqrt s) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hpos | hneg
  · left
    apply (eq_div_iff hΔ).2
    dsimp [s] at hpos ⊢
    nlinarith
  · right
    apply (eq_div_iff hΔ).2
    dsimp [s] at hneg ⊢
    nlinarith

theorem gap9 (x : ℝ) (hx : x ≠ 0) :
    deriv recip x = -(1 / x ^ 2) := by
  exact deriv_recip_formula x

theorem gap10 (x Δx θ : ℝ) (hx : x ≠ 0) (hxΔ : x + Δx ≠ 0)
    (hinc : recip (x + Δx) - recip x =
      Δx * deriv recip (x + θ * Δx)) :
    1 / (x + Δx) - 1 / x = -Δx / (x + θ * Δx) ^ 2 := by
  rw [deriv_recip_formula] at hinc
  simpa [recip, div_eq_mul_inv] using hinc

theorem gap11 (x Δx θ : ℝ) (hx : x ≠ 0) (hxΔ : x + Δx ≠ 0)
    (hinc : recip (x + Δx) - recip x =
      Δx * deriv recip (x + θ * Δx)) :
    θ ^ 2 * Δx ^ 2 + 2 * x * θ * Δx - x * Δx = 0 := by
  have heq := gap10 x Δx θ hx hxΔ hinc
  by_cases hΔ : Δx = 0
  · subst Δx
    ring
  have hy : x + θ * Δx ≠ 0 := by
    intro hy
    rw [hy] at heq
    simp at heq
    have hd0 : Δx = 0 := by
      field_simp [hx, hxΔ] at heq
      linarith
    exact hΔ hd0
  have hy' : x + Δx * θ ≠ 0 := by
    simpa [mul_comm] using hy
  field_simp [hx, hxΔ, hy, hy'] at heq
  ring_nf at heq
  have hp :
      Δx * (θ ^ 2 * Δx ^ 2 + 2 * x * θ * Δx - x * Δx) = 0 := by
    nlinarith [heq]
  exact (mul_eq_zero.mp hp).resolve_left hΔ

theorem gap12 (x Δx θ : ℝ) (hx : x ≠ 0) (hΔ : Δx ≠ 0)
    (hinc : recip (x + Δx) - recip x =
      Δx * deriv recip (x + θ * Δx)) :
    θ = x / Δx * (Real.sqrt (1 + Δx / x) - 1) ∨
      θ = x / Δx * (-Real.sqrt (1 + Δx / x) - 1) := by
  have heq :
      1 / (x + Δx) - 1 / x = -Δx / (x + θ * Δx) ^ 2 := by
    rw [deriv_recip_formula] at hinc
    simpa [recip, div_eq_mul_inv] using hinc
  have hxΔ : x + Δx ≠ 0 := by
    intro hend
    have hd : Δx = -x := by
      linarith
    have heq0 :
        -(1 / x) = x / (x + θ * (-x)) ^ 2 := by
      rw [hd] at heq
      simpa using heq
    by_cases hy : x + θ * (-x) = 0
    · rw [hy] at heq0
      simp [hx] at heq0
    · field_simp [hx, hy] at heq0
      have hnonneg : 0 ≤ 1 / (1 + -θ) ^ 2 :=
        div_nonneg (by norm_num) (sq_nonneg (1 + -θ))
      nlinarith [heq0, hnonneg]
  have hp := gap11 x Δx θ hx hxΔ hinc
  let r : ℝ := 1 + Δx / x
  have hsquare : (θ * Δx + x) ^ 2 = x ^ 2 * r := by
    dsimp [r]
    field_simp [hx]
    nlinarith [hp]
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hrnonneg : 0 ≤ r := by
    nlinarith [sq_nonneg (θ * Δx + x)]
  have hsqrt : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hrnonneg
  have hfactor :
      (θ * Δx + x - x * Real.sqrt r) *
        (θ * Δx + x + x * Real.sqrt r) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hpos | hneg
  · left
    change θ = x / Δx * (Real.sqrt r - 1)
    have ht : θ * Δx = x * (Real.sqrt r - 1) := by
      nlinarith [hpos]
    calc
      θ = (θ * Δx) / Δx := by field_simp [hΔ]
      _ = (x * (Real.sqrt r - 1)) / Δx := by rw [ht]
      _ = x / Δx * (Real.sqrt r - 1) := by ring
  · right
    change θ = x / Δx * (-Real.sqrt r - 1)
    have ht : θ * Δx = x * (-Real.sqrt r - 1) := by
      nlinarith [hneg]
    calc
      θ = (θ * Δx) / Δx := by field_simp [hΔ]
      _ = (x * (-Real.sqrt r - 1)) / Δx := by rw [ht]
      _ = x / Δx * (-Real.sqrt r - 1) := by ring

theorem gap13 (x : ℝ) :
    deriv Real.exp x = Real.exp x := by
  exact (Real.hasDerivAt_exp x).deriv

theorem gap14 (x Δx θ : ℝ)
    (hinc : Real.exp (x + Δx) - Real.exp x =
      Δx * deriv Real.exp (x + θ * Δx)) :
    Real.exp (x + Δx) - Real.exp x =
      Δx * Real.exp (x + θ * Δx) := by
  rw [gap13] at hinc
  exact hinc

theorem gap15 (Δx θ : ℝ) (hΔ : Δx ≠ 0)
    (hinc : Real.exp Δx - 1 = Δx * Real.exp (θ * Δx)) :
    θ = (1 / Δx) * Real.log ((Real.exp Δx - 1) / Δx) := by
  have hq :
      (Real.exp Δx - 1) / Δx = Real.exp (θ * Δx) := by
    apply (div_eq_iff hΔ).2
    nlinarith [hinc]
  rw [hq, Real.log_exp]
  field_simp [hΔ]

theorem gap16 (Δx θ : ℝ) (hΔ : Δx ≠ 0)
    (hθ : θ = (1 / Δx) * Real.log ((Real.exp Δx - 1) / Δx)) :
    0 < θ := by
  rw [hθ]
  rcases lt_or_gt_of_ne hΔ with hd | hd
  · have hnum : Real.exp Δx - 1 < 0 := by
      have he := (Real.exp_lt_one_iff).2 hd
      linarith
    have hqpos : 0 < (Real.exp Δx - 1) / Δx :=
      div_pos_of_neg_of_neg hnum hd
    have hconv := Real.add_one_lt_exp hΔ
    have hqone : (Real.exp Δx - 1) / Δx < 1 := by
      apply (div_lt_iff_of_neg hd).2
      nlinarith
    have hlog : Real.log ((Real.exp Δx - 1) / Δx) < 0 :=
      Real.log_neg hqpos hqone
    exact mul_pos_of_neg_of_neg (one_div_neg.mpr hd) hlog
  · have hconv := Real.add_one_lt_exp hΔ
    have hqone : 1 < (Real.exp Δx - 1) / Δx := by
      apply (lt_div_iff₀ hd).2
      nlinarith
    have hlog : 0 < Real.log ((Real.exp Δx - 1) / Δx) :=
      Real.log_pos hqone
    exact mul_pos (one_div_pos.mpr hd) hlog

theorem gap17 (Δx θ : ℝ) (hΔ : Δx ≠ 0)
    (hθ : θ = (1 / Δx) * Real.log ((Real.exp Δx - 1) / Δx)) :
    θ < 1 := by
  rw [hθ]
  have hneg : -Δx ≠ 0 := neg_ne_zero.mpr hΔ
  have hb := Real.add_one_lt_exp hneg
  have hm := mul_lt_mul_of_pos_right hb (Real.exp_pos Δx)
  have hexp : Real.exp (-Δx) * Real.exp Δx = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hexp] at hm
  have hbase : Real.exp Δx - 1 < Δx * Real.exp Δx := by
    nlinarith [hm]
  have hqpos : 0 < (Real.exp Δx - 1) / Δx := by
    rcases lt_or_gt_of_ne hΔ with hd | hd
    · exact div_pos_of_neg_of_neg
        (by have he := (Real.exp_lt_one_iff).2 hd; linarith) hd
    · exact div_pos
        (by have he := (Real.one_lt_exp_iff).2 hd; linarith) hd
  rcases lt_or_gt_of_ne hΔ with hd | hd
  · have hqexp :
        Real.exp Δx < (Real.exp Δx - 1) / Δx := by
      apply (lt_div_iff_of_neg hd).2
      nlinarith [hbase]
    have hlog :
        Δx < Real.log ((Real.exp Δx - 1) / Δx) := by
      have ht := Real.strictMonoOn_log (Real.exp_pos Δx) hqpos hqexp
      simpa using ht
    have hdiv :
        Real.log ((Real.exp Δx - 1) / Δx) / Δx < 1 := by
      apply (div_lt_iff_of_neg hd).2
      simpa using hlog
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  · have hqexp :
        (Real.exp Δx - 1) / Δx < Real.exp Δx := by
      apply (div_lt_iff₀ hd).2
      nlinarith [hbase]
    have hlog :
        Real.log ((Real.exp Δx - 1) / Δx) < Δx := by
      have ht := Real.strictMonoOn_log hqpos (Real.exp_pos Δx) hqexp
      simpa using ht
    have hdiv :
        Real.log ((Real.exp Δx - 1) / Δx) / Δx < 1 := by
      apply (div_lt_iff₀ hd).2
      simpa using hlog
    simpa [div_eq_mul_inv, mul_comm] using hdiv

theorem gap18 :
    (0 : ℝ) < 1 := by
  norm_num

end

end ProofGap.Exercise1246
