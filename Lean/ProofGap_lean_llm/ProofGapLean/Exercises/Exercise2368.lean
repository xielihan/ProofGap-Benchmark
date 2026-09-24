import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2368
noncomputable section

open Filter
open scoped Interval

def targetIntegrand (x : ℝ) : ℝ := Real.sin x ^ 2 / x
def oscillatoryIntegrand (x : ℝ) : ℝ := Real.cos (2 * x) / x

private theorem targetIntegrand_eq_sinc_mul (x : ℝ) :
    targetIntegrand x = Real.sinc x * Real.sin x := by
  by_cases hx : x = 0
  · simp [hx, targetIntegrand, Real.sinc]
  · simp [targetIntegrand, Real.sinc, hx, pow_two, div_eq_mul_inv,
      mul_left_comm, mul_comm]

private theorem continuous_targetIntegrand : Continuous targetIntegrand := by
  rw [funext targetIntegrand_eq_sinc_mul]
  exact Real.continuous_sinc.mul Real.continuous_sin

private theorem targetIntegrand_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable targetIntegrand MeasureTheory.volume a b :=
  continuous_targetIntegrand.intervalIntegrable a b

private theorem intervalIntegral_eq_sub_of_hasDerivAt
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (hcont : ContinuousOn f' (Set.uIcc a b)) :
    (∫ x in a..b, f' x) = f b - f a := by
  have hdiff : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ f x :=
    fun x hx => (hderiv x hx).differentiableAt
  have heq : ∀ x ∈ Set.uIcc a b, deriv f x = f' x :=
    fun x hx => (hderiv x hx).deriv
  have hcontDeriv : ContinuousOn (deriv f) (Set.uIcc a b) :=
    hcont.congr (fun x hx => heq x hx)
  have hfund :
      (∫ x in a..b, deriv f x) = f b - f a :=
    intervalIntegral.integral_deriv_eq_sub' f rfl hdiff hcontDeriv
  calc
    (∫ x in a..b, f' x) = ∫ x in a..b, deriv f x := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact (heq x hx).symm
    _ = f b - f a := hfund

private theorem oscillatory_intervalIntegrable (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable oscillatoryIntegrand MeasureTheory.volume a b := by
  unfold oscillatoryIntegrand
  apply ContinuousOn.intervalIntegrable
  apply (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn.div
    continuousOn_id
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  exact ne_of_gt (lt_of_lt_of_le ha hx.1)

private theorem oscillatory_tail_bound (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    |(∫ x in (1 : ℝ)..b, oscillatoryIntegrand x) -
      (∫ x in (1 : ℝ)..a, oscillatoryIntegrand x)| ≤ 1 / a := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  let r : ℝ → ℝ := fun x => Real.sin (2 * x) / (2 * x ^ 2)
  let q : ℝ → ℝ := fun x => 1 / (2 * x ^ 2)
  let Q : ℝ → ℝ := fun x => (Real.sin (2 * x) / 2) * x⁻¹
  let G : ℝ → ℝ := fun x => (-1 / 2 : ℝ) * x⁻¹
  have hoscCont : ContinuousOn oscillatoryIntegrand (Set.uIcc a b) := by
    unfold oscillatoryIntegrand
    apply (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).continuousOn.div continuousOn_id
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ne_of_gt (lt_of_lt_of_le ha0 hx.1)
  have hrCont : ContinuousOn r (Set.uIcc a b) := by
    dsimp [r]
    apply (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).continuousOn.div
      (continuousOn_const.mul (continuousOn_id.pow 2))
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_gt hx0))
  have hqCont : ContinuousOn q (Set.uIcc a b) := by
    dsimp [q]
    apply continuousOn_const.div
      (continuousOn_const.mul (continuousOn_id.pow 2))
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_gt hx0))
  have hosc1a := oscillatory_intervalIntegrable 1 a (by norm_num) ha
  have hoscab : IntervalIntegrable oscillatoryIntegrand
      MeasureTheory.volume a b := hoscCont.intervalIntegrable
  have hr : IntervalIntegrable r MeasureTheory.volume a b :=
    hrCont.intervalIntegrable
  have hq : IntervalIntegrable q MeasureTheory.volume a b :=
    hqCont.intervalIntegrable
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume) hosc1a hoscab
  have hdiff :
      (∫ x in (1 : ℝ)..b, oscillatoryIntegrand x) -
        (∫ x in (1 : ℝ)..a, oscillatoryIntegrand x) =
          ∫ x in a..b, oscillatoryIntegrand x := by
    linarith
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt Q (oscillatoryIntegrand x - r x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    have hs : HasDerivAt (fun y : ℝ => Real.sin (2 * y) / 2)
        (Real.cos (2 * x)) x := by
      convert (((Real.hasDerivAt_sin (2 * x)).comp x
        ((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x))).div_const 2) using 1 <;>
        ring
    have hi : HasDerivAt (fun y : ℝ => y⁻¹) (-1 / x ^ 2) x := by
      simpa using ((hasDerivAt_id x).inv (ne_of_gt hx0))
    dsimp [Q, oscillatoryIntegrand, r]
    convert (hs.mul hi) using 1 <;>
      field_simp [ne_of_gt hx0] <;> ring
  have hosc_eq :
      (∫ x in a..b, oscillatoryIntegrand x) =
        Q b - Q a + ∫ x in a..b, r x := by
    have hftc :
        (∫ x in a..b, oscillatoryIntegrand x - r x) = Q b - Q a :=
      intervalIntegral_eq_sub_of_hasDerivAt hderiv (hoscCont.sub hrCont)
    have hsub := intervalIntegral.integral_sub hoscab hr
    rw [hsub] at hftc
    linarith
  have hrq : ∀ x ∈ Set.Icc a b, |r x| ≤ q x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    dsimp [r, q]
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * x ^ 2)]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one (2 * x)) (by positivity)
  have hrbound : |∫ x in a..b, r x| ≤ 1 / (2 * a) - 1 / (2 * b) := by
    have hnorm : |∫ x in a..b, r x| ≤ ∫ x in a..b, |r x| := by
      simpa [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm
          (μ := MeasureTheory.volume) (f := r) hab)
    have habs : IntervalIntegrable (fun x => |r x|)
        MeasureTheory.volume a b := by
      simpa [Real.norm_eq_abs] using hr.norm
    have hmono : (∫ x in a..b, |r x|) ≤ ∫ x in a..b, q x :=
      intervalIntegral.integral_mono_on hab habs hq hrq
    have hderivq : ∀ x ∈ Set.uIcc a b, HasDerivAt G (q x) x := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
      have hi : HasDerivAt (fun y : ℝ => y⁻¹) (-1 / x ^ 2) x := by
        simpa using ((hasDerivAt_id x).inv (ne_of_gt hx0))
      dsimp [G, q]
      convert (hi.const_mul (-1 / 2 : ℝ)) using 1 <;>
        field_simp [ne_of_gt hx0] <;> ring
    have hqeval : (∫ x in a..b, q x) = 1 / (2 * a) - 1 / (2 * b) := by
      have hftc : (∫ x in a..b, q x) = G b - G a :=
        intervalIntegral_eq_sub_of_hasDerivAt hderivq hqCont
      calc
        (∫ x in a..b, q x) = G b - G a := hftc
        _ = 1 / (2 * a) - 1 / (2 * b) := by
          dsimp [G]
          field_simp [ne_of_gt ha0, ne_of_gt hb0] <;> ring
    rw [hqeval] at hmono
    exact hnorm.trans hmono
  have hQaform : Q a = Real.sin (2 * a) / (2 * a) := by
    dsimp [Q]
    field_simp [ne_of_gt ha0] <;> ring
  have hQbform : Q b = Real.sin (2 * b) / (2 * b) := by
    dsimp [Q]
    field_simp [ne_of_gt hb0] <;> ring
  have hQa : |Q a| ≤ 1 / (2 * a) := by
    rw [hQaform, abs_div, abs_of_pos (by positivity : 0 < 2 * a)]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one (2 * a)) (by positivity)
  have hQb : |Q b| ≤ 1 / (2 * b) := by
    rw [hQbform, abs_div, abs_of_pos (by positivity : 0 < 2 * b)]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one (2 * b)) (by positivity)
  rw [hdiff, hosc_eq]
  have htri1 :
      |Q b - Q a + ∫ x in a..b, r x| ≤
        |Q b - Q a| + |∫ x in a..b, r x| :=
    abs_add_le _ _
  have htri2 : |Q b - Q a| ≤ |Q b| + |Q a| := by
    simpa [sub_eq_add_neg] using abs_add_le (Q b) (-Q a)
  calc
    |Q b - Q a + ∫ x in a..b, r x| ≤
        |Q b - Q a| + |∫ x in a..b, r x| := htri1
    _ ≤ |Q b| + |Q a| + |∫ x in a..b, r x| :=
      add_le_add htri2 (le_refl _)
    _ ≤ 1 / (2 * b) + 1 / (2 * a) +
        (1 / (2 * a) - 1 / (2 * b)) := by linarith
    _ = 1 / a := by
      field_simp [ne_of_gt ha0, ne_of_gt hb0] <;> ring

private theorem oscillatory_integral_converges :
    ∃ L : ℝ,
      Tendsto (fun A => ∫ x in (1 : ℝ)..A, oscillatoryIntegrand x)
        atTop (nhds L) := by
  let O : ℝ → ℝ := fun A => ∫ x in (1 : ℝ)..A, oscillatoryIntegrand x
  have hc : Cauchy (Filter.map O atTop) := by
    rw [Metric.cauchy_iff]
    refine ⟨by infer_instance, ?_⟩
    intro ε hε
    let N : ℝ := 1 / ε + 1
    have hNpos : 0 < N := by
      dsimp [N]
      positivity
    have hN1 : 1 ≤ N := by
      dsimp [N]
      have h : 0 < 1 / ε := by positivity
      linarith
    have hsmall : 1 / N < ε := by
      rw [div_lt_iff₀ hNpos]
      have he : ε * N = 1 + ε := by
        dsimp [N]
        field_simp [ne_of_gt hε]
      rw [he]
      linarith
    refine ⟨O '' Set.Ici N, ?_, ?_⟩
    · change O ⁻¹' (O '' Set.Ici N) ∈ atTop
      filter_upwards [eventually_ge_atTop N] with x hx
      exact ⟨x, hx, rfl⟩
    · intro u hu v hv
      rcases hu with ⟨x, hx, rfl⟩
      rcases hv with ⟨y, hy, rfl⟩
      rcases le_total x y with hxy | hyx
      · have hx1 : 1 ≤ x := hN1.trans hx
        have hb : |O y - O x| ≤ 1 / x := by
          simpa [O] using oscillatory_tail_bound x y hx1 hxy
        have hdiv : 1 / x ≤ 1 / N := one_div_le_one_div_of_le hNpos hx
        rw [Real.dist_eq, abs_sub_comm]
        exact lt_of_le_of_lt (hb.trans hdiv) hsmall
      · have hy1 : 1 ≤ y := hN1.trans hy
        have hb : |O x - O y| ≤ 1 / y := by
          simpa [O] using oscillatory_tail_bound y x hy1 hyx
        have hdiv : 1 / y ≤ 1 / N := one_div_le_one_div_of_le hNpos hy
        rw [Real.dist_eq]
        exact lt_of_le_of_lt (hb.trans hdiv) hsmall
  rcases cauchy_iff_exists_le_nhds.mp hc with ⟨L, hL⟩
  refine ⟨L, ?_⟩
  simpa [O] using hL

theorem gap1 (x : ℝ) :
    targetIntegrand x = (1 - Real.cos (2 * x)) / (2 * x) := by
  unfold targetIntegrand
  have htrig : 1 - Real.cos (2 * x) = 2 * Real.sin x ^ 2 := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [htrig]
  by_cases hx : x = 0
  · simp [hx]
  · field_simp [hx]

theorem gap2 (x : ℝ) :
    (1 - Real.cos (2 * x)) / (2 * x) =
      (1 / 2 : ℝ) * (1 / x - Real.cos (2 * x) / x) := by
  by_cases hx : x = 0
  · simp [hx]
  · field_simp [hx]
    <;> ring

theorem gap3 (x : ℝ) :
    targetIntegrand x =
      (1 / 2 : ℝ) * (1 / x - Real.cos (2 * x) / x) := by
  rw [gap1 x, gap2 x]

theorem gap4 :
    Tendsto (fun A => ∫ x in (1 : ℝ)..A, 1 / x) atTop atTop := by
  refine Real.tendsto_log_atTop.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with A hA
  have hcont : ContinuousOn (fun x : ℝ => 1 / x) (Set.uIcc 1 A) := by
    apply continuousOn_const.div continuousOn_id
    intro x hx
    rw [Set.uIcc_of_le hA.le] at hx
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1)
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) A,
      HasDerivAt Real.log (1 / x) x := by
    intro x hx
    rw [Set.uIcc_of_le hA.le] at hx
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
    simpa [one_div] using Real.hasDerivAt_log (ne_of_gt hx0)
  have hlog :
      (∫ x in (1 : ℝ)..A, 1 / x) = Real.log A - Real.log 1 :=
    intervalIntegral_eq_sub_of_hasDerivAt hderiv hcont
  simpa using hlog.symm

theorem gap5 (A : ℝ) (hA : 1 < A) :
    |∫ x in (1 : ℝ)..A, Real.cos (2 * x)| ≤ 2 := by
  let F : ℝ → ℝ := fun y => Real.sin (2 * y) / 2
  have hderiv : ∀ x, HasDerivAt F (Real.cos (2 * x)) x := by
    intro x
    dsimp [F]
    convert (((Real.hasDerivAt_sin (2 * x)).comp x
      ((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x))).div_const 2) using 1 <;>
      ring
  have hInt :
      (∫ x in (1 : ℝ)..A, Real.cos (2 * x)) = F A - F 1 := by
    apply intervalIntegral_eq_sub_of_hasDerivAt
    · intro x hx
      exact hderiv x
    · exact (Real.continuous_cos.comp
        (continuous_const.mul continuous_id)).continuousOn
  rw [hInt]
  dsimp [F]
  have h1 := Real.abs_sin_le_one (2 * A)
  have h2 := Real.abs_sin_le_one 2
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem gap6 :
    Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0) := by
  simpa [one_div] using
    (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0))

theorem gap7 :
    ∃ L : ℝ,
      Tendsto (fun A => ∫ x in (1 : ℝ)..A, oscillatoryIntegrand x)
        atTop (nhds L) := by
  exact oscillatory_integral_converges

theorem gap8 :
    ¬ ∃ L : ℝ,
      Tendsto (fun A => ∫ x in (1 : ℝ)..A, targetIntegrand x)
        atTop (nhds L) := by
  rintro ⟨L, hL⟩
  rcases gap7 with ⟨M, hM⟩
  let H : ℝ → ℝ := fun A => ∫ x in (1 : ℝ)..A, 1 / x
  let T : ℝ → ℝ := fun A => ∫ x in (1 : ℝ)..A, targetIntegrand x
  let O : ℝ → ℝ := fun A => ∫ x in (1 : ℝ)..A, oscillatoryIntegrand x
  have heq : H =ᶠ[atTop] fun A => 2 * T A + O A := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with A hA
    have hone : IntervalIntegrable (fun x : ℝ => 1 / x)
        MeasureTheory.volume 1 A := by
      apply ContinuousOn.intervalIntegrable
      apply continuousOn_const.div continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le hA.le] at hx
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1)
    have hosc : IntervalIntegrable oscillatoryIntegrand
        MeasureTheory.volume 1 A :=
      oscillatory_intervalIntegrable 1 A (by norm_num) hA.le
    have hsplit :
        (∫ x in (1 : ℝ)..A, 1 / x - Real.cos (2 * x) / x) =
          (∫ x in (1 : ℝ)..A, 1 / x) -
            ∫ x in (1 : ℝ)..A, oscillatoryIntegrand x := by
      simpa [oscillatoryIntegrand] using
        (intervalIntegral.integral_sub hone hosc)
    have hT : T A = (1 / 2 : ℝ) * (H A - O A) := by
      calc
        T A = ∫ x in (1 : ℝ)..A,
            (1 / 2 : ℝ) * (1 / x - Real.cos (2 * x) / x) := by
              apply intervalIntegral.integral_congr
              intro x hx
              exact gap3 x
        _ = (1 / 2 : ℝ) *
            (∫ x in (1 : ℝ)..A, 1 / x - Real.cos (2 * x) / x) := by
              rw [intervalIntegral.integral_const_mul]
        _ = (1 / 2 : ℝ) * (H A - O A) := by
              rw [hsplit]
    dsimp [H, T, O]
    dsimp [H, T, O] at hT
    linarith
  have hfinite : Tendsto H atTop (nhds (2 * L + M)) := by
    have hs : Tendsto (fun A => 2 * T A + O A) atTop (nhds (2 * L + M)) :=
      (tendsto_const_nhds.mul hL).add hM
    exact hs.congr' heq.symm
  have hupper : ∀ᶠ A in atTop, H A < 2 * L + M + 1 :=
    (tendsto_order.1 hfinite).2 _ (by linarith)
  have hlower : ∀ᶠ A in atTop, 2 * L + M + 1 ≤ H A :=
    (tendsto_atTop.1 gap4) _
  rcases (hupper.and hlower).exists with ⟨A, hu, hl⟩
  linarith

theorem gap9 :
    ¬ ∃ L : ℝ,
      Tendsto (fun A => ∫ x in (0 : ℝ)..A, targetIntegrand x)
        atTop (nhds L) := by
  rintro ⟨L, hL⟩
  apply gap8
  let C : ℝ := ∫ x in (0 : ℝ)..(1 : ℝ), targetIntegrand x
  refine ⟨L - C, ?_⟩
  have hsub : Tendsto
      (fun A => (∫ x in (0 : ℝ)..A, targetIntegrand x) - C)
      atTop (nhds (L - C)) := hL.sub tendsto_const_nhds
  apply hsub.congr'
  filter_upwards with A
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume)
    (targetIntegrand_intervalIntegrable 0 1)
    (targetIntegrand_intervalIntegrable 1 A)
  dsimp [C]
  rw [← hsum]
  ring

end
end ProofGap.Exercise2368
