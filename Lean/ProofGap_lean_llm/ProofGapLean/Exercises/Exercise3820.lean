import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3820

noncomputable section

open Filter MeasureTheory Set
open scoped Interval

def integrand (α β x : ℝ) : ℝ :=
  (Real.sin (α * x) ^ 4 - Real.sin (β * x) ^ 4) / x

def HasValue (α β L : ℝ) : Prop :=
  Tendsto (fun A : ℝ => ∫ x in (0 : ℝ)..A, integrand α β x)
    atTop (nhds L)

def D (α β : ℝ) : ℝ :=
  sInf {L : ℝ | HasValue α β L}

def cosineDifference (p q x : ℝ) : ℝ :=
  (Real.cos (p * x) - Real.cos (q * x)) / x

def cosineDifferenceValue (p q : ℝ) : ℝ :=
  sInf {L : ℝ |
    Tendsto (fun A : ℝ => ∫ x in (0 : ℝ)..A, cosineDifference p q x)
      atTop (nhds L)}

private def ImproperHasValue (g : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∃ A > 0, ∀ a b : ℝ,
    0 < a → a ≤ δ → A ≤ b → |(∫ x in a..b, g x) - L| < ε

private theorem improper_neg {g : ℝ → ℝ} {L : ℝ}
    (h : ImproperHasValue g L) :
    ImproperHasValue (fun x => -g x) (-L) := by
  unfold ImproperHasValue at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, A, hA, hmain⟩ := h ε hε
  refine ⟨δ, hδ, A, hA, ?_⟩
  intro a b ha haδ hAb
  have hval := hmain a b ha haδ hAb
  rw [intervalIntegral.integral_neg]
  rw [show
    -(∫ x in a..b, g x) - -L =
      -((∫ x in a..b, g x) - L) by ring,
    abs_neg]
  exact hval

private theorem rectangle_sin_integrable (p q a b : ℝ) :
    Integrable
      (Function.uncurry (fun x s : ℝ => Real.sin (s * x)))
      ((volume.restrict (uIoc a b)).prod
        (volume.restrict (uIoc p q))) := by
  letI : Fact (volume (uIoc a b) < ⊤) := ⟨by
    rw [Real.volume_uIoc]
    exact ENNReal.ofReal_lt_top⟩
  letI : Fact (volume (uIoc p q) < ⊤) := ⟨by
    rw [Real.volume_uIoc]
    exact ENNReal.ofReal_lt_top⟩
  refine Integrable.of_bound (by fun_prop) 1 (by
    filter_upwards with z
    simpa only [Function.uncurry_apply_pair, Real.norm_eq_abs] using
      Real.abs_sin_le_one (z.2 * z.1))

private theorem finite_cos_diff_identity
    (p q a b : ℝ) (hpq : p ≤ q) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b,
      (Real.cos (p * x) - Real.cos (q * x)) / x) =
      ∫ s in p..q,
        (Real.cos (s * a) - Real.cos (s * b)) / s := by
  have hs_inner (x : ℝ) (hx : x ≠ 0) :
      (∫ s in p..q, Real.sin (s * x)) =
        (Real.cos (p * x) - Real.cos (q * x)) / x := by
    have hderiv (s : ℝ) :
        HasDerivAt (fun y : ℝ => -Real.cos (y * x) / x)
          (Real.sin (s * x)) s := by
      have hc :=
        (Real.hasDerivAt_cos (s * x)).comp s
          ((hasDerivAt_id s).mul_const x)
      convert hc.neg.div_const x using 1 <;>
        field_simp [hx]
    have h :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => hderiv s)
        ((by fun_prop : Continuous
          (fun s : ℝ => Real.sin (s * x))).intervalIntegrable p q)
    rw [h]
    field_simp [hx]
    ring
  have hx_inner (s : ℝ) :
      (∫ x in a..b, Real.sin (s * x)) =
        (Real.cos (s * a) - Real.cos (s * b)) / s := by
    by_cases hs : s = 0
    · subst s
      simp
    · have hderiv (x : ℝ) :
          HasDerivAt (fun y : ℝ => -Real.cos (s * y) / s)
            (Real.sin (s * x)) x := by
        have hc :=
          (Real.hasDerivAt_cos (s * x)).comp x
            ((hasDerivAt_id x).const_mul s)
        convert hc.neg.div_const s using 1 <;>
          field_simp [hs]
      have h :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x hx => hderiv x)
          ((by fun_prop : Continuous
            (fun x : ℝ => Real.sin (s * x))).intervalIntegrable a b)
      rw [h]
      field_simp [hs]
      ring
  calc
    (∫ x in a..b,
        (Real.cos (p * x) - Real.cos (q * x)) / x) =
        ∫ x in a..b, ∫ s in p..q, Real.sin (s * x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx0 : x ≠ 0 := by
        rw [uIcc_of_le hab] at hx
        exact ne_of_gt (ha.trans_le hx.1)
      exact (hs_inner x hx0).symm
    _ = ∫ s in p..q, ∫ x in a..b, Real.sin (s * x) := by
      simpa only [intervalIntegral.integral_of_le hpq,
        uIoc_of_le hpq] using
        intervalIntegral_integral_swap
          (rectangle_sin_integrable p q a b)
    _ = ∫ s in p..q,
        (Real.cos (s * a) - Real.cos (s * b)) / s := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact hx_inner s

private theorem integral_inv_pos
    (p q : ℝ) (hp : 0 < p) (hpq : p ≤ q) :
    (∫ s in p..q, (1 : ℝ) / s) =
      Real.log q - Real.log p := by
  have hderiv (s : ℝ) (hs : s ∈ uIcc p q) :
      HasDerivAt Real.log (1 / s) s := by
    rw [uIcc_of_le hpq] at hs
    simpa only [one_div] using
      Real.hasDerivAt_log (ne_of_gt (hp.trans_le hs.1))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv
    ((by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hpq]
      intro s hs
      exact (continuousAt_const.div continuousAt_id
        (ne_of_gt (hp.trans_le hs.1))).continuousWithinAt) :
      IntervalIntegrable (fun s : ℝ => 1 / s) volume p q)

private theorem near_cos_integral_bound
    (p q a : ℝ) (hp : 0 < p) (hpq : p ≤ q) :
    |∫ s in p..q, (Real.cos (s * a) - 1) / s| ≤
      |a| * (q - p) := by
  have hbound :
      ‖∫ s in p..q, (Real.cos (s * a) - 1) / s‖ ≤
        |a| * |q - p| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [uIoc_of_le hpq] at hs
    have hspos : 0 < s := hp.trans_le hs.1.le
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hspos]
    have hc :
        |Real.cos (s * a) - 1| ≤ |s * a| := by
      simpa only [Real.cos_zero, sub_zero] using
        Real.abs_cos_sub_cos_le (s * a) 0
    calc
      |Real.cos (s * a) - 1| / s ≤ |s * a| / s :=
        div_le_div_of_nonneg_right hc hspos.le
      _ = |a| := by
        rw [abs_mul, abs_of_pos hspos]
        field_simp
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hpq)] using
    hbound

private theorem oscillatory_cos_parameter_bound
    (p q b : ℝ) (hp : 0 < p) (hpq : p ≤ q) (hb : 0 < b) :
    |∫ s in p..q, Real.cos (s * b) / s| ≤
      2 / (p * b) + (q - p) / (p ^ 2 * b) := by
  let w : ℝ → ℝ := fun s => 1 / s
  let wp : ℝ → ℝ := fun s => -1 / s ^ 2
  let v : ℝ → ℝ := fun s => Real.sin (s * b) / b
  let vp : ℝ → ℝ := fun s => Real.cos (s * b)
  have hwderiv (s : ℝ) (hs : 0 < s) :
      HasDerivAt w (wp s) s := by
    have h := (hasDerivAt_const s (1 : ℝ)).div
      (hasDerivAt_id s) (ne_of_gt hs)
    convert h using 1 <;>
      dsimp [w, wp] <;>
      field_simp [ne_of_gt hs] <;> ring
  have hvderiv (s : ℝ) :
      HasDerivAt v (vp s) s := by
    have h :=
      (Real.hasDerivAt_sin (s * b)).comp s
        ((hasDerivAt_id s).mul_const b)
    convert h.div_const b using 1 <;>
      dsimp [v, vp] <;>
      field_simp [ne_of_gt hb] <;> ring
  have hwcont : ContinuousOn w (uIcc p q) := by
    rw [uIcc_of_le hpq]
    intro s hs
    exact (hwderiv s (hp.trans_le hs.1)).continuousAt.continuousWithinAt
  have hvcont : ContinuousOn v (uIcc p q) := by
    fun_prop
  have hwpint : IntervalIntegrable wp volume p q := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hpq]
    intro s hs
    have hs0 : s ≠ 0 := ne_of_gt (hp.trans_le hs.1)
    dsimp [wp]
    exact (continuousAt_const.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 hs0)).continuousWithinAt
  have hvpint : IntervalIntegrable vp volume p q := by
    exact (by fun_prop : Continuous vp).intervalIntegrable p q
  have hibp :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hwcont hvcont
      (fun s hs => hwderiv s
        (hp.trans (show p < s from (min_eq_left hpq ▸ hs.1))))
      (fun s hs => hvderiv s)
      hwpint hvpint
  have hibp' :
      (∫ s in p..q, Real.cos (s * b) / s) =
        w q * v q - w p * v p -
          ∫ s in p..q, wp s * v s := by
    simpa only [w, vp, one_div, div_eq_mul_inv,
      one_mul, mul_comm, mul_left_comm,
      mul_assoc] using hibp
  have hpqpos : 0 < q := hp.trans_le hpq
  have hqboundary :
      |w q * v q| ≤ 1 / (p * b) := by
    dsimp [w, v]
    rw [abs_mul, abs_div, abs_div, abs_one,
      abs_of_pos hpqpos, abs_of_pos hb]
    have hs := Real.abs_sin_le_one (q * b)
    calc
      (1 / q) * (|Real.sin (q * b)| / b) ≤
          (1 / p) * (1 / b) := by
        gcongr
      _ = 1 / (p * b) := by field_simp
  have hpboundary :
      |w p * v p| ≤ 1 / (p * b) := by
    dsimp [w, v]
    rw [abs_mul, abs_div, abs_div, abs_one,
      abs_of_pos hp, abs_of_pos hb]
    have hs := Real.abs_sin_le_one (p * b)
    calc
      (1 / p) * (|Real.sin (p * b)| / b) ≤
          (1 / p) * (1 / b) := by
        gcongr
      _ = 1 / (p * b) := by field_simp
  have hint :
      |∫ s in p..q, wp s * v s| ≤
        (1 / (p ^ 2 * b)) * (q - p) := by
    have h :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (a := p) (b := q) (C := 1 / (p ^ 2 * b))
        (f := fun s => wp s * v s) (by
          intro s hs
          rw [uIoc_of_le hpq] at hs
          have hspos : 0 < s := hp.trans_le hs.1.le
          dsimp [wp, v]
          rw [abs_mul, abs_div, abs_div,
            abs_neg, abs_one, abs_of_pos (sq_pos_of_pos hspos),
            abs_of_pos hb]
          have hsin := Real.abs_sin_le_one (s * b)
          have hsp : p ^ 2 ≤ s ^ 2 :=
            (sq_le_sq₀ hp.le hspos.le).2 hs.1.le
          calc
            (1 / s ^ 2) * (|Real.sin (s * b)| / b) ≤
                (1 / p ^ 2) * (1 / b) := by
              gcongr
            _ = 1 / (p ^ 2 * b) := by field_simp)
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hpq)] using h
  rw [hibp']
  calc
    |w q * v q - w p * v p -
        ∫ s in p..q, wp s * v s| ≤
        |w q * v q| + |w p * v p| +
          |∫ s in p..q, wp s * v s| := by
      calc
        |_ - _| ≤ |w q * v q - w p * v p| +
            |∫ s in p..q, wp s * v s| := abs_sub _ _
        _ ≤ (|w q * v q| + |w p * v p|) +
            |∫ s in p..q, wp s * v s| := by
          gcongr
          exact abs_sub _ _
    _ ≤ 1 / (p * b) + 1 / (p * b) +
        (1 / (p ^ 2 * b)) * (q - p) :=
      add_le_add (add_le_add hqboundary hpboundary) hint
    _ = 2 / (p * b) + (q - p) / (p ^ 2 * b) := by ring

private theorem cos_diff_improper_of_le
    (p q : ℝ) (hp : 0 < p) (hpq : p ≤ q) :
    ImproperHasValue
      (fun x : ℝ =>
        (Real.cos (p * x) - Real.cos (q * x)) / x)
      (Real.log (q / p)) := by
  unfold ImproperHasValue
  intro ε hε
  let d : ℝ := q - p
  let C : ℝ := 2 / p + d / p ^ 2
  let δ : ℝ := min 1 (ε / (4 * (d + 1)))
  let A : ℝ := 1 + 4 * C / ε
  have hd : 0 ≤ d := sub_nonneg.mpr hpq
  have hd1 : 0 < d + 1 := by linarith
  have hC : 0 < C := by
    dsimp [C]
    have hp2 : 0 < p ^ 2 := sq_pos_of_pos hp
    positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hA : 0 < A := by
    dsimp [A]
    positivity
  refine ⟨δ, hδ, A, hA, ?_⟩
  intro a b ha haδ hAb
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hab : a ≤ b := by
    have hA1 : 1 ≤ A := by
      dsimp [A]
      have : 0 ≤ 4 * C / ε := (div_pos (mul_pos (by norm_num) hC) hε).le
      linarith
    exact haδ.trans (hδ1.trans (hA1.trans hAb))
  have hb : 0 < b := hA.trans_le hAb
  have hfinite :=
    finite_cos_diff_identity p q a b hpq ha hab
  have hcosAint :
      IntervalIntegrable
        (fun s : ℝ => Real.cos (s * a) / s)
        volume p q := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hpq]
    intro s hs
    have hs0 : s ≠ 0 := ne_of_gt (hp.trans_le hs.1)
    have hc : ContinuousAt (fun y : ℝ => Real.cos (y * a)) s := by
      fun_prop
    exact (hc.div continuousAt_id hs0).continuousWithinAt
  have hcosBint :
      IntervalIntegrable
        (fun s : ℝ => Real.cos (s * b) / s)
        volume p q := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hpq]
    intro s hs
    have hs0 : s ≠ 0 := ne_of_gt (hp.trans_le hs.1)
    have hc : ContinuousAt (fun y : ℝ => Real.cos (y * b)) s := by
      fun_prop
    exact (hc.div continuousAt_id hs0).continuousWithinAt
  have hinvint :
      IntervalIntegrable (fun s : ℝ => 1 / s) volume p q := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hpq]
    intro s hs
    exact (continuousAt_const.div continuousAt_id
      (ne_of_gt (hp.trans_le hs.1))).continuousWithinAt
  have hsplit :
      (∫ s in p..q,
          (Real.cos (s * a) - Real.cos (s * b)) / s) =
        (∫ s in p..q, Real.cos (s * a) / s) -
          ∫ s in p..q, Real.cos (s * b) / s := by
    rw [← intervalIntegral.integral_sub hcosAint hcosBint]
    apply intervalIntegral.integral_congr
    intro s hs
    ring
  have hnear_eq :
      (∫ s in p..q, Real.cos (s * a) / s) -
          (Real.log q - Real.log p) =
        ∫ s in p..q, (Real.cos (s * a) - 1) / s := by
    rw [← integral_inv_pos p q hp hpq,
      ← intervalIntegral.integral_sub hcosAint hinvint]
    apply intervalIntegral.integral_congr
    intro s hs
    ring
  have hnear :
      |(∫ s in p..q, Real.cos (s * a) / s) -
          (Real.log q - Real.log p)| < ε / 4 := by
    rw [hnear_eq]
    refine (near_cos_integral_bound p q a hp hpq).trans_lt ?_
    rw [abs_of_pos ha]
    have hδfrac : δ ≤ ε / (4 * (d + 1)) :=
      min_le_right _ _
    have hmul :
        a * d ≤ (ε / (4 * (d + 1))) * d :=
      mul_le_mul_of_nonneg_right (haδ.trans hδfrac) hd
    calc
      a * (q - p) = a * d := by rfl
      _ ≤ (ε / (4 * (d + 1))) * d := hmul
      _ < ε / 4 := by
        have hratio : d / (d + 1) < 1 := by
          rw [div_lt_one hd1]
          linarith
        calc
          (ε / (4 * (d + 1))) * d =
              (ε / 4) * (d / (d + 1)) := by
            field_simp
          _ < (ε / 4) * 1 :=
            mul_lt_mul_of_pos_left hratio (by positivity)
          _ = ε / 4 := by ring
  have hosc :
      |∫ s in p..q, Real.cos (s * b) / s| < ε / 4 := by
    refine (oscillatory_cos_parameter_bound p q b hp hpq hb).trans_lt ?_
    have hboundC :
        2 / (p * b) + (q - p) / (p ^ 2 * b) = C / b := by
      dsimp [C, d]
      field_simp [ne_of_gt hp, ne_of_gt hb]
    rw [hboundC]
    have hAgt : 4 * C / ε < A := by
      dsimp [A]
      linarith
    have hbgt : 4 * C / ε < b := hAgt.trans_le hAb
    have hfour : 0 < 4 * C / ε := by positivity
    have hdiv :
        C / b < C / (4 * C / ε) :=
      (div_lt_div_iff_of_pos_left hC hb hfour).2 hbgt
    calc
      C / b < C / (4 * C / ε) := hdiv
      _ = ε / 4 := by
        field_simp [ne_of_gt hC, ne_of_gt hε]
  have hlog :
      Real.log (q / p) = Real.log q - Real.log p := by
    rw [Real.log_div (ne_of_gt (hp.trans_le hpq))
      (ne_of_gt hp)]
  rw [hfinite, hsplit, hlog]
  calc
    |(∫ s in p..q, Real.cos (s * a) / s) -
          (∫ s in p..q, Real.cos (s * b) / s) -
          (Real.log q - Real.log p)| =
        |((∫ s in p..q, Real.cos (s * a) / s) -
            (Real.log q - Real.log p)) -
          (∫ s in p..q, Real.cos (s * b) / s)| := by
      congr 1
      ring
    _ ≤ |(∫ s in p..q, Real.cos (s * a) / s) -
            (Real.log q - Real.log p)| +
          |∫ s in p..q, Real.cos (s * b) / s| :=
      abs_sub _ _
    _ < ε / 4 + ε / 4 := add_lt_add hnear hosc
    _ < ε := by linarith

private theorem cos_diff_improper
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    ImproperHasValue
      (fun x : ℝ =>
        (Real.cos (p * x) - Real.cos (q * x)) / x)
      (Real.log (q / p)) := by
  rcases le_total p q with hpq | hqp
  · exact cos_diff_improper_of_le p q hp hpq
  · have hbase := cos_diff_improper_of_le q p hq hqp
    have hneg := improper_neg hbase
    convert hneg using 1
    · funext x
      ring
    · rw [Real.log_div (ne_of_gt hq) (ne_of_gt hp),
        Real.log_div (ne_of_gt hp) (ne_of_gt hq)]
      ring

private theorem improper_half_eighth
    {f g : ℝ → ℝ} {L M : ℝ}
    (hfint : ∀ a b : ℝ, 0 < a → a ≤ b →
      IntervalIntegrable f volume a b)
    (hgint : ∀ a b : ℝ, 0 < a → a ≤ b →
      IntervalIntegrable g volume a b)
    (hf : ImproperHasValue f L)
    (hg : ImproperHasValue g M) :
    ImproperHasValue
      (fun x => (1 / 2 : ℝ) * f x + (1 / 8 : ℝ) * g x)
      ((1 / 2 : ℝ) * L + (1 / 8 : ℝ) * M) := by
  unfold ImproperHasValue at hf hg ⊢
  intro ε hε
  obtain ⟨δf, hδf, Af, hAf, hfm⟩ := hf (ε / 2) (by positivity)
  obtain ⟨δg, hδg, Ag, hAg, hgm⟩ := hg (ε / 2) (by positivity)
  let δ : ℝ := min 1 (min δf δg)
  let A : ℝ := max 1 (max Af Ag)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨δ, hδ, A, hA, ?_⟩
  intro a b ha haδ hAb
  have haδf : a ≤ δf :=
    haδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have haδg : a ≤ δg :=
    haδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hAaf : Af ≤ A :=
    (le_max_left Af Ag).trans (le_max_right 1 (max Af Ag))
  have hAag : Ag ≤ A :=
    (le_max_right Af Ag).trans (le_max_right 1 (max Af Ag))
  have hferr := hfm a b ha haδf (hAaf.trans hAb)
  have hgerr := hgm a b ha haδg (hAag.trans hAb)
  have hab : a ≤ b := by
    have ha1 : a ≤ 1 := haδ.trans (min_le_left _ _)
    exact ha1.trans ((le_max_left 1 (max Af Ag)).trans hAb)
  have hfi := hfint a b ha hab
  have hgi := hgint a b ha hab
  rw [intervalIntegral.integral_add
    (hfi.const_mul (1 / 2 : ℝ))
    (hgi.const_mul (1 / 8 : ℝ)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  calc
    |(1 / 2 : ℝ) * (∫ x in a..b, f x) +
          (1 / 8 : ℝ) * (∫ x in a..b, g x) -
          ((1 / 2 : ℝ) * L + (1 / 8 : ℝ) * M)| =
        |(1 / 2 : ℝ) * ((∫ x in a..b, f x) - L) +
          (1 / 8 : ℝ) * ((∫ x in a..b, g x) - M)| := by
      congr 1
      ring
    _ ≤ |(1 / 2 : ℝ) * ((∫ x in a..b, f x) - L)| +
          |(1 / 8 : ℝ) * ((∫ x in a..b, g x) - M)| :=
      abs_add_le _ _
    _ = (1 / 2 : ℝ) * |(∫ x in a..b, f x) - L| +
          (1 / 8 : ℝ) * |(∫ x in a..b, g x) - M| := by
      rw [abs_mul, abs_mul]
      norm_num
    _ < (1 / 2 : ℝ) * (ε / 2) +
          (1 / 8 : ℝ) * (ε / 2) := by
      exact add_lt_add
        (mul_lt_mul_of_pos_left hferr (by norm_num))
        (mul_lt_mul_of_pos_left hgerr (by norm_num))
    _ < ε := by linarith

private theorem cos_mul_eq_cos_abs_mul (c x : ℝ) :
    Real.cos (c * x) = Real.cos (|c| * x) := by
  by_cases hc : 0 ≤ c
  · rw [abs_of_nonneg hc]
  · have hcneg : c < 0 := lt_of_not_ge hc
    rw [abs_of_neg hcneg,
      show (-c) * x = -(c * x) by ring,
      Real.cos_neg]

private theorem sin_fourth_identity (z : ℝ) :
    Real.sin z ^ 4 =
      (3 - 4 * Real.cos (2 * z) + Real.cos (4 * z)) / 8 := by
  rw [show Real.sin z ^ 4 = (Real.sin z ^ 2) ^ 2 by ring,
    Real.sin_sq,
    show (4 : ℝ) * z = 2 * (2 * z) by ring,
    Real.cos_two_mul,
    Real.cos_two_mul (2 * z),
    Real.cos_two_mul]
  ring

private theorem sin_fourth_difference_kernel
    (α β x : ℝ) :
    (Real.sin (α * x) ^ 4 - Real.sin (β * x) ^ 4) / x =
      (1 / 2 : ℝ) *
          ((Real.cos ((2 * |β|) * x) -
            Real.cos ((2 * |α|) * x)) / x) +
        (1 / 8 : ℝ) *
          ((Real.cos ((4 * |α|) * x) -
            Real.cos ((4 * |β|) * x)) / x) := by
  rw [sin_fourth_identity, sin_fourth_identity]
  rw [show 2 * (α * x) = (2 * α) * x by ring,
    show 4 * (α * x) = (4 * α) * x by ring,
    show 2 * (β * x) = (2 * β) * x by ring,
    show 4 * (β * x) = (4 * β) * x by ring]
  rw [cos_mul_eq_cos_abs_mul (2 * α) x,
    cos_mul_eq_cos_abs_mul (4 * α) x,
    cos_mul_eq_cos_abs_mul (2 * β) x,
    cos_mul_eq_cos_abs_mul (4 * β) x]
  rw [abs_mul, abs_mul, abs_mul, abs_mul]
  norm_num
  ring

private theorem sin_fourth_diff_improper_nonzero
    (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0) :
    ImproperHasValue
      (fun x : ℝ =>
        (Real.sin (α * x) ^ 4 - Real.sin (β * x) ^ 4) / x)
      (3 / 8 * Real.log |α / β|) := by
  let f : ℝ → ℝ := fun x =>
    (Real.cos ((2 * |β|) * x) -
      Real.cos ((2 * |α|) * x)) / x
  let g : ℝ → ℝ := fun x =>
    (Real.cos ((4 * |α|) * x) -
      Real.cos ((4 * |β|) * x)) / x
  have habsa : 0 < |α| := abs_pos.mpr hα
  have habsb : 0 < |β| := abs_pos.mpr hβ
  have hf :
      ImproperHasValue f
        (Real.log ((2 * |α|) / (2 * |β|))) := by
    exact cos_diff_improper
      (2 * |β|) (2 * |α|) (by positivity) (by positivity)
  have hg :
      ImproperHasValue g
        (Real.log ((4 * |β|) / (4 * |α|))) := by
    exact cos_diff_improper
      (4 * |α|) (4 * |β|) (by positivity) (by positivity)
  have hfint :
      ∀ a b : ℝ, 0 < a → a ≤ b →
        IntervalIntegrable f volume a b := by
    intro a b ha hab
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (ha.trans_le hx.1)
    dsimp [f]
    apply ContinuousAt.continuousWithinAt
    exact
      ((Real.continuous_cos.comp
          (continuous_const.mul continuous_id)).sub
        (Real.continuous_cos.comp
          (continuous_const.mul continuous_id))).continuousAt.div
        continuousAt_id hx0
  have hgint :
      ∀ a b : ℝ, 0 < a → a ≤ b →
        IntervalIntegrable g volume a b := by
    intro a b ha hab
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (ha.trans_le hx.1)
    dsimp [g]
    apply ContinuousAt.continuousWithinAt
    exact
      ((Real.continuous_cos.comp
          (continuous_const.mul continuous_id)).sub
        (Real.continuous_cos.comp
          (continuous_const.mul continuous_id))).continuousAt.div
        continuousAt_id hx0
  have hcomb :=
    improper_half_eighth hfint hgint hf hg
  convert hcomb using 1
  · funext x
    exact sin_fourth_difference_kernel α β x
  · have hr1 :
        (2 * |α|) / (2 * |β|) = |α| / |β| := by
      field_simp [ne_of_gt habsa, ne_of_gt habsb]
    have hr2 :
        (4 * |β|) / (4 * |α|) = |β| / |α| := by
      field_simp [ne_of_gt habsa, ne_of_gt habsb]
    rw [hr1, hr2, abs_div,
      Real.log_div (ne_of_gt habsa) (ne_of_gt habsb),
      Real.log_div (ne_of_gt habsb) (ne_of_gt habsa)]
    ring

private def single (α x : ℝ) : ℝ :=
  Real.sin (α * x) ^ 4 / x

private theorem single_eq_sinc (α x : ℝ) (hα : α ≠ 0) :
    single α x =
      α * Real.sin (α * x) ^ 3 * Real.sinc (α * x) := by
  by_cases hx : x = 0
  · simp [single, hx]
  · have hax : α * x ≠ 0 := mul_ne_zero hα hx
    rw [Real.sinc_of_ne_zero hax]
    dsimp [single]
    field_simp [hα, hx]

private theorem continuous_single (α : ℝ) (hα : α ≠ 0) :
    Continuous (single α) := by
  rw [show single α =
      fun x : ℝ =>
        α * Real.sin (α * x) ^ 3 * Real.sinc (α * x) by
    funext x
    exact single_eq_sinc α x hα]
  exact
    (continuous_const.mul
      ((Real.continuous_sin.comp
        (continuous_const.mul continuous_id)).pow 3)).mul
      (Real.continuous_sinc.comp
        (continuous_const.mul continuous_id))

private theorem improper_sub
    {f g : ℝ → ℝ} {L M : ℝ}
    (hfcont : Continuous f) (hgcont : Continuous g)
    (hf : ImproperHasValue f L)
    (hg : ImproperHasValue g M) :
    ImproperHasValue (fun x => f x - g x) (L - M) := by
  unfold ImproperHasValue at hf hg ⊢
  intro ε hε
  obtain ⟨δf, hδf, Af, hAf, hfm⟩ :=
    hf (ε / 2) (by positivity)
  obtain ⟨δg, hδg, Ag, hAg, hgm⟩ :=
    hg (ε / 2) (by positivity)
  let δ : ℝ := min δf δg
  let A : ℝ := max Af Ag
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hA : 0 < A := hAf.trans_le (le_max_left _ _)
  refine ⟨δ, hδ, A, hA, ?_⟩
  intro a b ha haδ hAb
  have hferr :=
    hfm a b ha (haδ.trans (min_le_left _ _))
      ((le_max_left _ _).trans hAb)
  have hgerr :=
    hgm a b ha (haδ.trans (min_le_right _ _))
      ((le_max_right _ _).trans hAb)
  rw [intervalIntegral.integral_sub
    (hfcont.intervalIntegrable a b)
    (hgcont.intervalIntegrable a b)]
  calc
    |((∫ x in a..b, f x) - (∫ x in a..b, g x)) -
        (L - M)| =
        |((∫ x in a..b, f x) - L) -
          ((∫ x in a..b, g x) - M)| := by
      congr 1
      ring
    _ ≤ |(∫ x in a..b, f x) - L| +
          |(∫ x in a..b, g x) - M| :=
      abs_sub _ _
    _ < ε / 2 + ε / 2 := add_lt_add hferr hgerr
    _ = ε := by ring

private theorem improper_unique
    {f : ℝ → ℝ} {L M : ℝ}
    (hL : ImproperHasValue f L)
    (hM : ImproperHasValue f M) :
    L = M := by
  by_contra hne
  have hdist : 0 < |L - M| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨δL, hδL, AL, hAL, hLm⟩ :=
    hL (|L - M| / 3) (by positivity)
  obtain ⟨δM, hδM, AM, hAM, hMm⟩ :=
    hM (|L - M| / 3) (by positivity)
  let a : ℝ := min δL δM / 2
  let b : ℝ := max AL AM
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have haL : a ≤ δL := by
    dsimp [a]
    have hm : min δL δM ≤ δL := min_le_left _ _
    nlinarith [hδL, hδM]
  have haM : a ≤ δM := by
    dsimp [a]
    have hm : min δL δM ≤ δM := min_le_right _ _
    nlinarith [hδL, hδM]
  have hbL : AL ≤ b := le_max_left _ _
  have hbM : AM ≤ b := le_max_right _ _
  have hLe := hLm a b ha haL hbL
  have hMe := hMm a b ha haM hbM
  have htri :
      |L - M| ≤
        |(∫ x in a..b, f x) - L| +
          |(∫ x in a..b, f x) - M| := by
    calc
      |L - M| =
          |-( ((∫ x in a..b, f x) - L)) +
            ((∫ x in a..b, f x) - M)| := by
        congr 1
        ring
      _ ≤ |-((∫ x in a..b, f x) - L)| +
          |(∫ x in a..b, f x) - M| :=
        abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have :
      |L - M| < |L - M| / 3 + |L - M| / 3 :=
    htri.trans_lt (add_lt_add hLe hMe)
  linarith

private theorem integral_single_scale
    (α c a b : ℝ) (hα : α ≠ 0) (hc : c ≠ 0) :
    (∫ x in a..b, single (c * α) x) =
      ∫ u in c * a..c * b, single α u := by
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv
      (a := a) (b := b)
      (f := fun x : ℝ => c * x)
      (f' := fun _ : ℝ => c)
      (g := single α)
      (fun x hx => by
        convert
          ((hasDerivAt_const x c).mul
            (hasDerivAt_id x)) using 1 <;> simp)
      continuousOn_const
      (continuous_single α hα)
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro x hx
  change single (c * α) x = single α (c * x) * c
  by_cases hx0 : x = 0
  · simp [single, hx0]
  · dsimp [single]
    field_simp [hc, hx0]

private theorem improper_single_scale
    (α c L : ℝ) (hα : α ≠ 0) (hc : 0 < c)
    (h : ImproperHasValue (single α) L) :
    ImproperHasValue (single (c * α)) L := by
  unfold ImproperHasValue at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, A, hA, hm⟩ := h ε hε
  refine ⟨δ / c, by positivity, A / c, by positivity, ?_⟩
  intro a b ha haδ hAb
  have hca : 0 < c * a := mul_pos hc ha
  have hcaδ : c * a ≤ δ := by
    have := (le_div_iff₀ hc).mp haδ
    simpa [mul_comm] using this
  have hAcb : A ≤ c * b := by
    have := (div_le_iff₀ hc).mp hAb
    simpa [mul_comm] using this
  rw [integral_single_scale α c a b hα (ne_of_gt hc)]
  exact hm (c * a) (c * b) hca hcaδ hAcb

private theorem single_not_improper
    (α : ℝ) (hα : α ≠ 0) :
    ¬ ∃ L : ℝ, ImproperHasValue (single α) L := by
  rintro ⟨L, hL⟩
  have h2α : 2 * α ≠ 0 := mul_ne_zero (by norm_num) hα
  have hscaled :
      ImproperHasValue (single (2 * α)) L :=
    improper_single_scale α 2 L hα (by norm_num) hL
  have hzero :
      ImproperHasValue
        (fun x : ℝ =>
          (Real.sin (α * x) ^ 4 -
            Real.sin ((2 * α) * x) ^ 4) / x)
        0 := by
    have hsub :=
      improper_sub
        (continuous_single α hα)
        (continuous_single (2 * α) h2α)
        hL hscaled
    convert hsub using 1
    · funext x
      dsimp [single]
      ring
    · ring
  have hformula :=
    sin_fourth_diff_improper_nonzero α (2 * α) hα h2α
  have heq :=
    improper_unique hformula hzero
  have habsα : 0 < |α| := abs_pos.mpr hα
  have hratio : |α / (2 * α)| = (1 / 2 : ℝ) := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    field_simp [ne_of_gt habsα]
  rw [hratio] at heq
  have hloghalf : Real.log (1 / 2 : ℝ) ≠ 0 := by
    rw [Real.log_ne_zero]
    norm_num
  exact hloghalf (by
    have : (3 / 8 : ℝ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp heq).resolve_left this)

private theorem improperHasValue_to_tendsto
    {g : ℝ → ℝ} {L : ℝ}
    (hg : Continuous g) (h : ImproperHasValue g L) :
    Tendsto (fun A : ℝ => ∫ x in (0 : ℝ)..A, g x)
      atTop (nhds L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, A, hA, hmain⟩ :=
    h (ε / 2) (by positivity)
  let F : ℝ → ℝ := fun a => ∫ x in (0 : ℝ)..a, g x
  have hF :
      Tendsto F (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    have hcont :
        ContinuousAt F 0 :=
      (intervalIntegral.differentiable_integral_of_continuous
        (a := (0 : ℝ)) hg).continuous.continuousAt
    simpa [F] using hcont.tendsto.mono_left inf_le_left
  have hsmall :
      ∀ᶠ a in nhdsWithin 0 (Ioi (0 : ℝ)),
        dist (F a) 0 < ε / 2 :=
    (Metric.tendsto_nhds.1 hF) (ε / 2) (by positivity)
  have hδevent :
      ∀ᶠ a in nhdsWithin 0 (Ioi (0 : ℝ)), a < δ :=
    (show ∀ᶠ a in nhds (0 : ℝ), a < δ from
      Iio_mem_nhds hδ).filter_mono inf_le_left
  have hAevent :
      ∀ᶠ a in nhdsWithin 0 (Ioi (0 : ℝ)), a < A :=
    (show ∀ᶠ a in nhds (0 : ℝ), a < A from
      Iio_mem_nhds hA).filter_mono inf_le_left
  have hex :
      ∀ᶠ a in nhdsWithin 0 (Ioi (0 : ℝ)),
        0 < a ∧ a < δ ∧ a < A ∧ dist (F a) 0 < ε / 2 := by
    filter_upwards [self_mem_nhdsWithin, hδevent, hAevent, hsmall]
      with a ha haδ haA haSmall
    exact ⟨ha, haδ, haA, haSmall⟩
  obtain ⟨a, ha, haδ, haA, haSmall⟩ := hex.exists
  refine ⟨A, ?_⟩
  intro b hb
  have hab : a ≤ b := haA.le.trans hb
  have htail := hmain a b ha haδ.le hb
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable (μ := volume) 0 a)
      (hg.intervalIntegrable (μ := volume) a b)
  rw [Real.dist_eq, ← hadd]
  calc
    |(∫ x in (0 : ℝ)..a, g x) +
          (∫ x in a..b, g x) - L| =
        |(∫ x in (0 : ℝ)..a, g x) +
          ((∫ x in a..b, g x) - L)| := by
        congr 1
        ring
    _ ≤ |∫ x in (0 : ℝ)..a, g x| +
          |(∫ x in a..b, g x) - L| :=
      abs_add_le _ _
    _ < ε / 2 + ε / 2 := by
      have hnear :
          |∫ x in (0 : ℝ)..a, g x| < ε / 2 := by
        simpa [F, Real.dist_eq] using haSmall
      exact add_lt_add hnear htail
    _ = ε := by ring

private theorem tendsto_to_improperHasValue
    {g : ℝ → ℝ} {L : ℝ}
    (hg : Continuous g)
    (h : Tendsto (fun A : ℝ => ∫ x in (0 : ℝ)..A, g x)
      atTop (nhds L)) :
    ImproperHasValue g L := by
  unfold ImproperHasValue
  intro ε hε
  obtain ⟨A, htail⟩ :=
    (Metric.tendsto_atTop.1 h) (ε / 2) (by positivity)
  let F : ℝ → ℝ := fun a => ∫ x in (0 : ℝ)..a, g x
  have hF :
      Tendsto F (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    have hcont :
        ContinuousAt F 0 :=
      (intervalIntegral.differentiable_integral_of_continuous
        (a := (0 : ℝ)) hg).continuous.continuousAt
    simpa [F] using hcont.tendsto.mono_left inf_le_left
  obtain ⟨δ, hδ, hnear⟩ :=
    (Metric.tendsto_nhdsWithin_nhds.1 hF)
      (ε / 2) (by positivity)
  let d : ℝ := δ / 2
  let B : ℝ := max A 1
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right A 1)
  refine ⟨d, hd, B, hB, ?_⟩
  intro a b ha had hBb
  have haδ : dist a 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ha]
    dsimp [d] at had
    linarith
  have hnearA :
      |∫ x in (0 : ℝ)..a, g x| < ε / 2 := by
    have hm := hnear (show a ∈ Ioi (0 : ℝ) from ha) haδ
    simpa [F, Real.dist_eq] using hm
  have hAb : A ≤ b := (le_max_left A 1).trans hBb
  have htailB := htail b hAb
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable (μ := volume) 0 a)
      (hg.intervalIntegrable (μ := volume) a b)
  have hrewrite :
      (∫ x in a..b, g x) =
        (∫ x in (0 : ℝ)..b, g x) -
          ∫ x in (0 : ℝ)..a, g x := by
    linarith
  rw [hrewrite]
  calc
    |(∫ x in (0 : ℝ)..b, g x) -
          (∫ x in (0 : ℝ)..a, g x) - L| =
        |((∫ x in (0 : ℝ)..b, g x) - L) -
          ∫ x in (0 : ℝ)..a, g x| := by
        congr 1
        ring
    _ ≤ |(∫ x in (0 : ℝ)..b, g x) - L| +
          |∫ x in (0 : ℝ)..a, g x| :=
      abs_sub _ _
    _ < ε / 2 + ε / 2 := by
      simpa only [Real.dist_eq] using add_lt_add htailB hnearA
    _ = ε := by ring

private theorem continuous_integrand_nonzero
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Continuous (integrand a b) := by
  rw [show integrand a b =
      fun x : ℝ => single a x - single b x by
    funext x
    unfold integrand single
    ring]
  exact (continuous_single a ha).sub (continuous_single b hb)

private def cosineDifferenceContinuousForm (p q x : ℝ) : ℝ :=
  -2 * Real.sin (((p + q) / 2) * x) *
    (((p - q) / 2) * Real.sinc (((p - q) / 2) * x))

private theorem cosineDifference_eq_continuousForm (p q : ℝ) :
    cosineDifference p q = cosineDifferenceContinuousForm p q := by
  funext x
  by_cases hpq : p = q
  · subst q
    simp [cosineDifference, cosineDifferenceContinuousForm]
  · by_cases hx : x = 0
    · subst x
      simp [cosineDifference, cosineDifferenceContinuousForm]
    · have hc : (p - q) / 2 ≠ 0 := by
        exact div_ne_zero (sub_ne_zero.mpr hpq) (by norm_num)
      have hcx : (p - q) / 2 * x ≠ 0 :=
        mul_ne_zero hc hx
      unfold cosineDifference cosineDifferenceContinuousForm
      rw [Real.sinc_of_ne_zero hcx]
      rw [show p * x =
            ((p + q) / 2) * x + ((p - q) / 2) * x by ring,
        show q * x =
            ((p + q) / 2) * x - ((p - q) / 2) * x by ring,
        Real.cos_add, Real.cos_sub]
      field_simp [hx, hc, sub_ne_zero.mpr hpq]
      ring

private theorem continuous_cosineDifference (p q : ℝ) :
    Continuous (cosineDifference p q) := by
  rw [cosineDifference_eq_continuousForm p q]
  unfold cosineDifferenceContinuousForm
  fun_prop

private theorem improper_cosineDifference
    (p q : ℝ) (hp : p ≠ 0) (hq : q ≠ 0) :
    ImproperHasValue (cosineDifference p q)
      (Real.log |q / p|) := by
  have hpabs : 0 < |p| := abs_pos.mpr hp
  have hqabs : 0 < |q| := abs_pos.mpr hq
  have h :=
    cos_diff_improper |p| |q| hpabs hqabs
  convert h using 1
  · funext x
    unfold cosineDifference
    rw [← cos_mul_eq_cos_abs_mul p x,
      ← cos_mul_eq_cos_abs_mul q x]
  · rw [abs_div]

private theorem cosineDifference_hasValue
    (p q : ℝ) (hp : p ≠ 0) (hq : q ≠ 0) :
    Tendsto
      (fun A : ℝ =>
        ∫ x in (0 : ℝ)..A, cosineDifference p q x)
      atTop (nhds (Real.log |q / p|)) :=
  improperHasValue_to_tendsto
    (continuous_cosineDifference p q)
    (improper_cosineDifference p q hp hq)

private theorem hasValue_unique
    {a b L M : ℝ} (hL : HasValue a b L) (hM : HasValue a b M) :
    L = M :=
  tendsto_nhds_unique hL hM

private theorem D_eq_of_hasValue
    {a b L : ℝ} (h : HasValue a b L) :
    D a b = L := by
  have hset :
      {M : ℝ | HasValue a b M} = {L} := by
    ext M
    constructor
    · intro hM
      exact (hasValue_unique hM h).symm ▸ Set.mem_singleton L
    · intro hM
      simpa only [Set.mem_singleton_iff] using hM ▸ h
  unfold D
  rw [hset]
  exact csInf_singleton L

private theorem cosineDifferenceValue_eq
    (p q : ℝ) (hp : p ≠ 0) (hq : q ≠ 0) :
    cosineDifferenceValue p q = Real.log |q / p| := by
  have h := cosineDifference_hasValue p q hp hq
  have hset :
      {L : ℝ |
        Tendsto
          (fun A : ℝ =>
            ∫ x in (0 : ℝ)..A, cosineDifference p q x)
          atTop (nhds L)} =
        {Real.log |q / p|} := by
    ext L
    constructor
    · intro hL
      have heq := tendsto_nhds_unique hL h
      simpa only [Set.mem_singleton_iff] using heq
    · intro hL
      simpa only [Set.mem_singleton_iff] using hL ▸ h
  unfold cosineDifferenceValue
  rw [hset]
  exact csInf_singleton _

private theorem integrand_hasValue_nonzero
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    HasValue a b (3 / 8 * Real.log |a / b|) := by
  exact improperHasValue_to_tendsto
    (continuous_integrand_nonzero a b ha hb)
    (sin_fourth_diff_improper_nonzero a b ha hb)

private theorem D_eq_formula
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    D a b = 3 / 8 * Real.log |a / b| :=
  D_eq_of_hasValue (integrand_hasValue_nonzero a b ha hb)

theorem gap1 (x : ℝ) :
    Real.sin x ^ 4 =
      1 / 8 * (Real.cos (4 * x) - 4 * Real.cos (2 * x) + 3) := by
  rw [sin_fourth_identity x]
  ring

theorem gap2 (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0) :
    D α β =
      1 / 8 * cosineDifferenceValue (4 * α) (4 * β) -
        1 / 2 * cosineDifferenceValue (2 * α) (2 * β) := by
  rw [D_eq_formula α β hα hβ,
    cosineDifferenceValue_eq (4 * α) (4 * β)
      (mul_ne_zero (by norm_num) hα)
      (mul_ne_zero (by norm_num) hβ),
    cosineDifferenceValue_eq (2 * α) (2 * β)
      (mul_ne_zero (by norm_num) hα)
      (mul_ne_zero (by norm_num) hβ)]
  have h4 :
      |(4 * β) / (4 * α)| = |β / α| := by
    congr 1
    field_simp [hα]
  have h2 :
      |(2 * β) / (2 * α)| = |β / α| := by
    congr 1
    field_simp [hα]
  have hlog :
      Real.log |β / α| = -Real.log |α / β| := by
    rw [abs_div, abs_div,
      Real.log_div (abs_ne_zero.mpr hβ) (abs_ne_zero.mpr hα),
      Real.log_div (abs_ne_zero.mpr hα) (abs_ne_zero.mpr hβ)]
    ring
  rw [h4, h2, hlog]
  ring

theorem gap3 (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0) :
    D α β =
      1 / 8 * Real.log |β / α| -
        1 / 2 * Real.log |β / α| := by
  rw [D_eq_formula α β hα hβ]
  have hlog :
      Real.log |β / α| = -Real.log |α / β| := by
    rw [abs_div, abs_div,
      Real.log_div (abs_ne_zero.mpr hβ) (abs_ne_zero.mpr hα),
      Real.log_div (abs_ne_zero.mpr hα) (abs_ne_zero.mpr hβ)]
    ring
  rw [hlog]
  ring

theorem gap4 (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0) :
    D α β = 3 / 8 * Real.log |α / β| :=
  D_eq_formula α β hα hβ

theorem gap5 (α β : ℝ) (hαβ : α = β) (hβ : β = 0) :
    D α β = 0 := by
  subst α
  subst β
  apply D_eq_of_hasValue
  unfold HasValue
  simpa [integrand] using
    (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0))

theorem gap6 (α β : ℝ) (hα : α = 0) (hβ : β ≠ 0) :
    ¬ ∃ L : ℝ, HasValue α β L := by
  subst α
  rintro ⟨L, hL⟩
  have hg : Continuous (integrand 0 β) := by
    rw [show integrand 0 β =
        fun x : ℝ => -single β x by
      funext x
      unfold integrand single
      simp only [zero_mul, Real.sin_zero, zero_pow, zero_sub]
      ring]
    exact (continuous_single β hβ).neg
  have himp :=
    tendsto_to_improperHasValue hg hL
  have hneg := improper_neg himp
  apply single_not_improper β hβ
  refine ⟨-L, ?_⟩
  convert hneg using 1
  funext x
  unfold integrand single
  simp
  ring

theorem gap7 (β α : ℝ) (hβ : β = 0) (hα : α ≠ 0) :
    ¬ ∃ L : ℝ, HasValue α β L := by
  subst β
  rintro ⟨L, hL⟩
  have hg : Continuous (integrand α 0) := by
    rw [show integrand α 0 = single α by
      funext x
      unfold integrand single
      simp]
    exact continuous_single α hα
  have himp :=
    tendsto_to_improperHasValue hg hL
  apply single_not_improper α hα
  refine ⟨L, ?_⟩
  convert himp using 1
  funext x
  unfold integrand single
  simp

end

end ProofGap.Exercise3820
