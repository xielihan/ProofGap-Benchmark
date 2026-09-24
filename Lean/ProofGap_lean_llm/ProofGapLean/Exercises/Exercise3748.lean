import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3748

noncomputable section

open Filter Set
open scoped Interval Topology

def integrand (p x : ℝ) : ℝ :=
  Real.sin x / (Real.rpow x p + Real.sin x)

def partialIntegral (p A : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..A, integrand p x

def Converges (p : ℝ) : Prop :=
  (∀ A : ℝ, 0 < A →
    IntervalIntegrable (integrand p) MeasureTheory.volume 0 A) ∧
  ∃ L : ℝ, Tendsto (partialIntegral p) atTop (𝓝 L)

def sineModel (p x : ℝ) : ℝ :=
  Real.sin x / Real.rpow x p

def cosineCorrection (p x : ℝ) : ℝ :=
  Real.cos (2 * x) /
    (Real.rpow x p * (Real.rpow x p + 1))

def positiveModelPlus (p x : ℝ) : ℝ :=
  1 / (Real.rpow x p * (Real.rpow x p + 1))

def positiveModelMinus (p x : ℝ) : ℝ :=
  1 / (Real.rpow x p * (Real.rpow x p - 1))

def remainder (p x : ℝ) : ℝ :=
  (Real.sin x) ^ 2 /
    (Real.rpow x p * (Real.rpow x p + Real.sin x))

def TailConverges (f : ℝ → ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (fun A : ℝ => ∫ x in (2 : ℝ)..A, f x) atTop (𝓝 L)

def rightLimitValue (p : ℝ) : ℝ :=
  if 1 < p then 1 else if p = 1 then 1 / 2 else 0

private lemma tendsto_rpow_nhdsGT_zero_of_pos
    (q : ℝ) (hq : 0 < q) :
    Tendsto (fun x : ℝ => Real.rpow x q)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hneg :
      Tendsto (fun x : ℝ => Real.rpow x (-q))
        (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr hq)
  have hinv := hneg.inv_tendsto_atTop
  apply hinv.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hr :
      Real.rpow x (-q) = (Real.rpow x q)⁻¹ := by
    simpa only using Real.rpow_neg hx.le q
  change (Real.rpow x (-q))⁻¹ = Real.rpow x q
  rw [hr, inv_inv]

private lemma tendsto_sinc_nhdsGT_zero :
    Tendsto Real.sinc
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  simpa using
    (Real.continuous_sinc.tendsto 0).mono_left inf_le_left

private lemma integrand_eq_sinc_form
    (p x : ℝ) (hx : 0 < x) :
    integrand p x =
      Real.sinc x /
        (Real.rpow x (p - 1) + Real.sinc x) := by
  have hx0 : x ≠ 0 := hx.ne'
  have hsin := Real.sinc_of_ne_zero hx0
  have hr :
      Real.rpow x p =
        x * Real.rpow x (p - 1) := by
    calc
      Real.rpow x p =
          Real.rpow x (1 + (p - 1)) := by ring
      _ = Real.rpow x 1 *
          Real.rpow x (p - 1) :=
        Real.rpow_add hx 1 (p - 1)
      _ = x * Real.rpow x (p - 1) := by
        have hr1 : Real.rpow x 1 = x := by
          simpa only using Real.rpow_one x
        rw [hr1]
  have hsx : Real.sin x = x * Real.sinc x := by
    rw [hsin]
    field_simp
  unfold integrand
  rw [hsx, hr]
  field_simp [hx0]

theorem gap1 (p : ℝ) (hp : 0 < p) :
    Tendsto (integrand p) (𝓝[>] (0 : ℝ)) (𝓝 (rightLimitValue p)) := by
  by_cases hpgt : 1 < p
  · have hpow :=
      tendsto_rpow_nhdsGT_zero_of_pos
        (p - 1) (sub_pos.mpr hpgt)
    have hden :=
      hpow.add tendsto_sinc_nhdsGT_zero
    have hquot :=
      tendsto_sinc_nhdsGT_zero.div hden (by norm_num)
    have heq :
        integrand p =ᶠ[(𝓝[>] (0 : ℝ))]
          (fun x =>
            Real.sinc x /
              (Real.rpow x (p - 1) + Real.sinc x)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact integrand_eq_sinc_form p x hx
    simpa [rightLimitValue, hpgt] using
      hquot.congr' heq.symm
  · by_cases hpeq : p = 1
    · subst p
      have hden :
          Tendsto
            (fun x : ℝ =>
              Real.rpow x ((1 : ℝ) - 1) + Real.sinc x)
            (𝓝[>] (0 : ℝ)) (𝓝 2) := by
        have hone :
            Tendsto
              (fun _ : ℝ => (1 : ℝ))
              (𝓝[>] (0 : ℝ)) (𝓝 1) :=
          tendsto_const_nhds
        have hs := hone.add tendsto_sinc_nhdsGT_zero
        convert hs using 1 <;> norm_num
      have hquot :=
        tendsto_sinc_nhdsGT_zero.div hden (by norm_num)
      have heq :
          integrand 1 =ᶠ[(𝓝[>] (0 : ℝ))]
            (fun x =>
              Real.sinc x /
                (Real.rpow x ((1 : ℝ) - 1) +
                  Real.sinc x)) := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact integrand_eq_sinc_form 1 x hx
      simpa [rightLimitValue] using
        hquot.congr' heq.symm
    · have hplt : p < 1 := lt_of_le_of_ne
        (le_of_not_gt hpgt) hpeq
      have hpow :
          Tendsto (fun x : ℝ => Real.rpow x (p - 1))
            (𝓝[>] (0 : ℝ)) atTop :=
        tendsto_rpow_neg_nhdsGT_zero (sub_neg.mpr hplt)
      have hlower :
          Tendsto
            (fun x : ℝ => -1 + Real.rpow x (p - 1))
            (𝓝[>] (0 : ℝ)) atTop :=
        tendsto_const_nhds.add_atTop hpow
      have hden :
          Tendsto
            (fun x : ℝ =>
              Real.rpow x (p - 1) + Real.sinc x)
            (𝓝[>] (0 : ℝ)) atTop := by
        apply tendsto_atTop_mono
          (fun x => by
            have hs := (abs_le.mp
              (Real.abs_sinc_le_one x)).1
            linarith)
          hlower
      have hquot :
          Tendsto
            (fun x : ℝ =>
              Real.sinc x /
                (Real.rpow x (p - 1) + Real.sinc x))
            (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_bdd_div_atTop_nhds_zero
          (Filter.Eventually.of_forall
            (fun x => (abs_le.mp
              (Real.abs_sinc_le_one x)).1))
          (Filter.Eventually.of_forall Real.sinc_le_one)
          hden
      have heq :
          integrand p =ᶠ[(𝓝[>] (0 : ℝ))]
            (fun x =>
              Real.sinc x /
                (Real.rpow x (p - 1) + Real.sinc x)) := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact integrand_eq_sinc_form p x hx
      simpa [rightLimitValue, hpgt, hpeq] using
        hquot.congr' heq.symm

theorem gap2 (p : ℝ) (hp : 0 < p) :
    ∃ l : ℝ, Tendsto (integrand p) (𝓝[>] (0 : ℝ)) (𝓝 l) := by
  exact ⟨rightLimitValue p, gap1 p hp⟩

theorem gap3 (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    integrand p x = sineModel p x - remainder p x := by
  have hrpos : 0 < Real.rpow x p :=
    Real.rpow_pos_of_pos hx p
  have hdenpos :
      0 < Real.rpow x p + Real.sin x := by
    by_cases hx1 : x ≤ 1
    · have hsinpos : 0 < Real.sin x :=
        Real.sin_pos_of_pos_of_lt_pi hx
          (hx1.trans_lt
            (lt_of_lt_of_le one_lt_two Real.two_le_pi))
      positivity
    · have hxgt : 1 < x := lt_of_not_ge hx1
      have hrgt : 1 < Real.rpow x p :=
        Real.one_lt_rpow hxgt hp
      have hsge : -1 ≤ Real.sin x :=
        Real.neg_one_le_sin x
      linarith
  unfold integrand sineModel remainder
  field_simp [hrpos.ne', hdenpos.ne']
  ring

private lemma sine_correction_integrableOn_Ioi
    (p : ℝ) (hp : 0 < p) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ =>
        p * Real.cos x * Real.rpow x (-p - 1))
      (Set.Ioi 2) := by
  have hpow :
      MeasureTheory.IntegrableOn
        (fun x : ℝ => Real.rpow x (-p - 1))
        (Set.Ioi 2) :=
    integrableOn_Ioi_rpow_of_lt
      (by linarith) (by norm_num)
  have hmajor :=
    hpow.const_mul p
  refine hmajor.mono' ?_ ?_
  · have hcont :
        ContinuousOn
          (fun x : ℝ =>
            p * Real.cos x * Real.rpow x (-p - 1))
          (Set.Ioi 2) := by
      intro x hx
      have hx2 : 2 < x := hx
      have hx0 : x ≠ 0 := by linarith
      exact (continuousAt_const.mul
        Real.continuous_cos.continuousAt |>.mul
          (Real.continuousAt_rpow_const x (-p - 1)
            (Or.inl hx0))).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards
      [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with x hx
    have hx2 : 2 < x := hx
    have hx0 : 0 ≤ x := by linarith
    have hr0 :
        0 ≤ Real.rpow x (-p - 1) :=
      Real.rpow_nonneg hx0 _
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos hp, abs_of_nonneg hr0]
    have hmul :
        |Real.cos x| * Real.rpow x (-p - 1) ≤
          Real.rpow x (-p - 1) :=
      mul_le_of_le_one_left hr0 (Real.abs_cos_le_one x)
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hmul hp.le)

private lemma sine_model_integral_identity
    (p A : ℝ) (hp : 0 < p) (hA : 2 ≤ A) :
    (∫ x in (2 : ℝ)..A, sineModel p x) =
      (-Real.cos A * Real.rpow A (-p)) -
        (-Real.cos 2 * Real.rpow 2 (-p)) -
        ∫ x in (2 : ℝ)..A,
          p * Real.cos x * Real.rpow x (-p - 1) := by
  let F : ℝ → ℝ :=
    fun x => -Real.cos x * Real.rpow x (-p)
  let f : ℝ → ℝ :=
    fun x =>
      Real.sin x * Real.rpow x (-p) +
        p * Real.cos x * Real.rpow x (-p - 1)
  have hderiv :
      ∀ x ∈ Set.uIcc (2 : ℝ) A,
        HasDerivAt F (f x) x := by
    intro x hx
    rw [Set.uIcc_of_le hA] at hx
    have hxpos : 0 < x := by linarith [hx.1]
    have hr :=
      Real.hasDerivAt_rpow_const
        (x := x) (p := -p) (Or.inl hxpos.ne')
    have h :=
      Real.hasDerivAt_cos x |>.neg.mul hr
    convert h using 1
    · dsimp [f]
      ring
  have hfInt :
      IntervalIntegrable f MeasureTheory.volume 2 A := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hA] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    dsimp [f]
    exact ((Real.continuous_sin.continuousAt.mul
      (Real.continuousAt_rpow_const x (-p)
        (Or.inl hx0))).add
          ((continuousAt_const.mul
            Real.continuous_cos.continuousAt).mul
              (Real.continuousAt_rpow_const x (-p - 1)
                (Or.inl hx0)))).continuousWithinAt
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      hderiv hfInt
  have hsinInt :
      IntervalIntegrable
        (fun x : ℝ =>
          Real.sin x * Real.rpow x (-p))
        MeasureTheory.volume 2 A := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hA] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    exact (Real.continuous_sin.continuousAt.mul
      (Real.continuousAt_rpow_const x (-p)
        (Or.inl hx0))).continuousWithinAt
  have hcorrInt :
      IntervalIntegrable
        (fun x : ℝ =>
          p * Real.cos x * Real.rpow x (-p - 1))
        MeasureTheory.volume 2 A := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hA]
    exact (sine_correction_integrableOn_Ioi p hp).mono_set
      Set.Ioc_subset_Ioi_self
  have hsplit :
      (∫ x in (2 : ℝ)..A, f x) =
        (∫ x in (2 : ℝ)..A,
          Real.sin x * Real.rpow x (-p)) +
        ∫ x in (2 : ℝ)..A,
          p * Real.cos x * Real.rpow x (-p - 1) := by
    exact intervalIntegral.integral_add hsinInt hcorrInt
  rw [hsplit] at hFTC
  have hsine :
      (∫ x in (2 : ℝ)..A, sineModel p x) =
        ∫ x in (2 : ℝ)..A,
          Real.sin x * Real.rpow x (-p) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hA] at hx
    have hx0 : 0 ≤ x := by linarith [hx.1]
    have hr :
        Real.rpow x (-p) =
          (Real.rpow x p)⁻¹ := by
      simpa only using Real.rpow_neg hx0 p
    unfold sineModel
    change Real.sin x / Real.rpow x p =
      Real.sin x * Real.rpow x (-p)
    rw [hr]
    ring
  rw [hsine]
  calc
    _ = F A - F 2 -
        ∫ x in (2 : ℝ)..A,
          p * Real.cos x * Real.rpow x (-p - 1) := by
      linarith [hFTC]
    _ = _ := by rfl

theorem gap4 (p : ℝ) (hp : 0 < p) :
    TailConverges (sineModel p) := by
  let G : ℝ :=
    ∫ x : ℝ in Set.Ioi 2,
      p * Real.cos x * Real.rpow x (-p - 1)
  let C : ℝ :=
    -(-Real.cos 2 * Real.rpow 2 (-p)) - G
  have hF :
      Tendsto
        (fun A : ℝ =>
          -Real.cos A * Real.rpow A (-p))
        atTop (𝓝 0) := by
    have hpow :=
      tendsto_rpow_neg_atTop hp
    exact bdd_le_mul_tendsto_zero
      (b := (-1 : ℝ)) (B := 1)
      (Filter.Eventually.of_forall
        (fun A => by
          have h := Real.cos_le_one A
          linarith))
      (Filter.Eventually.of_forall
        (fun A => by
          have h := Real.neg_one_le_cos A
          linarith))
      hpow
  have hcorr :
      Tendsto
        (fun A : ℝ =>
          ∫ x in (2 : ℝ)..A,
            p * Real.cos x * Real.rpow x (-p - 1))
        atTop (𝓝 G) := by
    simpa [G] using
      (MeasureTheory.intervalIntegral_tendsto_integral_Ioi
        2 (sine_correction_integrableOn_Ioi p hp)
        tendsto_id)
  have hlimit :
      Tendsto
        (fun A : ℝ =>
          (-Real.cos A * Real.rpow A (-p)) -
            (-Real.cos 2 * Real.rpow 2 (-p)) -
            ∫ x in (2 : ℝ)..A,
              p * Real.cos x * Real.rpow x (-p - 1))
        atTop (𝓝 C) := by
    simpa [C] using
      (hF.sub_const
        (-Real.cos 2 * Real.rpow 2 (-p))).sub hcorr
  refine ⟨C, ?_⟩
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with A hA
  exact (sine_model_integral_identity p A hp hA).symm

private lemma rpow_gt_one_on_tail
    (p x : ℝ) (hp : 0 < p) (hx : 2 ≤ x) :
    1 < Real.rpow x p :=
  Real.one_lt_rpow (one_lt_two.trans_le hx) hp

private lemma half_model_identity
    (p x : ℝ) (hp : 0 < p) (hx : 2 ≤ x) :
    (1 / 2 : ℝ) *
        (positiveModelPlus p x - cosineCorrection p x) =
      (Real.sin x) ^ 2 /
        (Real.rpow x p * (Real.rpow x p + 1)) := by
  have hrpos :
      0 < Real.rpow x p :=
    Real.rpow_pos_of_pos (by linarith) p
  have hplus :
      Real.rpow x p + 1 ≠ 0 := by positivity
  unfold positiveModelPlus cosineCorrection
  rw [Real.cos_two_mul, Real.sin_sq]
  field_simp [hrpos.ne', hplus]
  ring

theorem gap5 (p x : ℝ) (hp : 0 < p) (hx : 2 ≤ x) :
    0 ≤
      (1 / 2 : ℝ) *
        (positiveModelPlus p x - cosineCorrection p x) := by
  rw [half_model_identity p x hp hx]
  have hrpos :
      0 < Real.rpow x p :=
    Real.rpow_pos_of_pos (by linarith) p
  exact div_nonneg (sq_nonneg _)
    (mul_nonneg hrpos.le (by positivity))

theorem gap6 (p x : ℝ) (hp : 0 < p) (hx : 2 ≤ x) :
    (1 / 2 : ℝ) *
        (positiveModelPlus p x - cosineCorrection p x) =
      (Real.sin x) ^ 2 /
        (Real.rpow x p * (Real.rpow x p + 1)) := by
  exact half_model_identity p x hp hx

theorem gap7 (p x : ℝ) (hp : 0 < p) (hx : 2 ≤ x) :
    (Real.sin x) ^ 2 /
        (Real.rpow x p * (Real.rpow x p + 1)) ≤
      remainder p x := by
  let r : ℝ := Real.rpow x p
  have hrpos : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (by linarith) p
  have hrgt : 1 < r := by
    dsimp [r]
    exact rpow_gt_one_on_tail p x hp hx
  have hactual :
      0 < r * (r + Real.sin x) := by
    have hs := Real.neg_one_le_sin x
    have : 0 < r + Real.sin x := by linarith
    positivity
  have hden :
      r * (r + Real.sin x) ≤ r * (r + 1) := by
    exact mul_le_mul_of_nonneg_left
      (by linarith [Real.sin_le_one x]) hrpos.le
  unfold remainder
  change
    Real.sin x ^ 2 / (r * (r + 1)) ≤
      Real.sin x ^ 2 / (r * (r + Real.sin x))
  exact div_le_div_of_nonneg_left
    (sq_nonneg _) hactual hden

theorem gap8 (p x : ℝ) (hp : 0 < p) (hx : 2 ≤ x) :
    remainder p x ≤
      (Real.sin x) ^ 2 /
        (Real.rpow x p * (Real.rpow x p - 1)) := by
  let r : ℝ := Real.rpow x p
  have hrpos : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (by linarith) p
  have hrgt : 1 < r := by
    dsimp [r]
    exact rpow_gt_one_on_tail p x hp hx
  have hminus :
      0 < r * (r - 1) :=
    mul_pos hrpos (sub_pos.mpr hrgt)
  have hden :
      r * (r - 1) ≤ r * (r + Real.sin x) := by
    exact mul_le_mul_of_nonneg_left
      (by linarith [Real.neg_one_le_sin x]) hrpos.le
  unfold remainder
  change
    Real.sin x ^ 2 / (r * (r + Real.sin x)) ≤
      Real.sin x ^ 2 / (r * (r - 1))
  exact div_le_div_of_nonneg_left
    (sq_nonneg _) hminus hden

theorem gap9 (p x : ℝ) (hp : 0 < p) (hx : 2 ≤ x) :
    (Real.sin x) ^ 2 /
        (Real.rpow x p * (Real.rpow x p - 1)) ≤
      positiveModelMinus p x := by
  let r : ℝ := Real.rpow x p
  have hrgt : 1 < r := by
    dsimp [r]
    exact rpow_gt_one_on_tail p x hp hx
  have hden :
      0 < r * (r - 1) := by
    have hrpos : 0 < r := zero_lt_one.trans hrgt
    exact mul_pos hrpos (sub_pos.mpr hrgt)
  have hsin :
      Real.sin x ^ 2 ≤ 1 := by
    have habs := Real.abs_sin_le_one x
    have hsquare :=
      (sq_le_sq₀ (abs_nonneg (Real.sin x))
        zero_le_one).2 habs
    simpa only [sq_abs, one_pow] using hsquare
  unfold positiveModelMinus
  change Real.sin x ^ 2 / (r * (r - 1)) ≤
    1 / (r * (r - 1))
  exact div_le_div_of_nonneg_right hsin hden.le

theorem gap10 (p x : ℝ) (hp : 0 < p) (hx : 2 ≤ x) :
    0 ≤ positiveModelMinus p x := by
  unfold positiveModelMinus
  have hrgt :
      1 < Real.rpow x p :=
    rpow_gt_one_on_tail p x hp hx
  have hrpos :
      0 < Real.rpow x p := zero_lt_one.trans hrgt
  exact div_nonneg zero_le_one
    (mul_nonneg hrpos.le (sub_nonneg.mpr hrgt.le))

private def plusWeightDerivative (p x : ℝ) : ℝ :=
  -(p * Real.rpow x (p - 1) *
      (2 * Real.rpow x p + 1)) /
    (Real.rpow x p * (Real.rpow x p + 1)) ^ 2

private lemma hasDerivAt_positiveModelPlus
    (p x : ℝ) (hx : 0 < x) :
    HasDerivAt (positiveModelPlus p)
      (plusWeightDerivative p x) x := by
  have hr :=
    Real.hasDerivAt_rpow_const
      (x := x) (p := p) (Or.inl hx.ne')
  have hden :=
    hr.mul (hr.add_const 1)
  have hden0 :
      Real.rpow x p * (Real.rpow x p + 1) ≠ 0 := by
    have hrpos := Real.rpow_pos_of_pos hx p
    positivity
  have h :=
    (hasDerivAt_const (x := x) (c := (1 : ℝ))).div
      hden hden0
  convert h using 1
  dsimp [positiveModelPlus, plusWeightDerivative]
  field_simp [hden0]
  ring

private lemma plusWeightDerivative_nonpos
    (p x : ℝ) (hp : 0 < p) (hx : 2 < x) :
    plusWeightDerivative p x ≤ 0 := by
  have hx0 : 0 ≤ x := by linarith
  have hrpos :
      0 < Real.rpow x p :=
    Real.rpow_pos_of_pos (by linarith) p
  have hrderiv :
      0 ≤ Real.rpow x (p - 1) :=
    Real.rpow_nonneg hx0 _
  unfold plusWeightDerivative
  have hnum :
      0 ≤ p * Real.rpow x (p - 1) *
        (2 * Real.rpow x p + 1) := by positivity
  have hden :
      0 ≤
        (Real.rpow x p *
          (Real.rpow x p + 1)) ^ 2 := sq_nonneg _
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr hnum) hden

private lemma tendsto_positiveModelPlus_atTop_zero
    (p : ℝ) (hp : 0 < p) :
    Tendsto (positiveModelPlus p) atTop (𝓝 0) := by
  have hr :
      Tendsto (fun x : ℝ => Real.rpow x p)
        atTop atTop :=
    tendsto_rpow_atTop hp
  have hden :
      Tendsto
        (fun x : ℝ =>
          Real.rpow x p * (Real.rpow x p + 1))
        atTop atTop :=
    hr.atTop_mul_atTop₀
      (tendsto_atTop_add_const_right atTop 1 hr)
  change Tendsto
    (fun x : ℝ =>
      1 / (Real.rpow x p *
        (Real.rpow x p + 1))) atTop (𝓝 0)
  simpa only [one_div] using hden.inv_tendsto_atTop

private lemma plusWeightDerivative_integrableOn_Ioi
    (p : ℝ) (hp : 0 < p) :
    MeasureTheory.IntegrableOn
      (plusWeightDerivative p) (Set.Ioi 2) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonpos'
    (fun x hx => by
      have hx2 : 2 ≤ x := hx
      exact hasDerivAt_positiveModelPlus p x
        (by linarith))
    (fun x hx =>
      plusWeightDerivative_nonpos p x hp hx)
    (tendsto_positiveModelPlus_atTop_zero p hp)

private lemma sine_two_mul_plusWeightDerivative_integrableOn_Ioi
    (p : ℝ) (hp : 0 < p) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ =>
        (Real.sin (2 * x) / 2) *
          plusWeightDerivative p x)
      (Set.Ioi 2) := by
  have hderiv :=
    plusWeightDerivative_integrableOn_Ioi p hp
  change MeasureTheory.Integrable _
    (MeasureTheory.volume.restrict (Set.Ioi 2))
  change MeasureTheory.Integrable _
    (MeasureTheory.volume.restrict (Set.Ioi 2)) at hderiv
  refine MeasureTheory.Integrable.mono hderiv ?_ ?_
  · have hcont :
        ContinuousOn
          (fun x : ℝ =>
            (Real.sin (2 * x) / 2) *
              plusWeightDerivative p x)
          (Set.Ioi 2) := by
      intro x hx
      have hx2 : 2 < x := hx
      have hxpos : 0 < x := by linarith [hx]
      have hr :
          ContinuousAt (fun y : ℝ => Real.rpow y p) x :=
        Real.continuousAt_rpow_const x p (Or.inl hxpos.ne')
      have hrm :
          ContinuousAt (fun y : ℝ => Real.rpow y (p - 1)) x :=
        Real.continuousAt_rpow_const x (p - 1)
          (Or.inl hxpos.ne')
      have hden0 :
          Real.rpow x p * (Real.rpow x p + 1) ≠ 0 := by
        have hrpos := Real.rpow_pos_of_pos hxpos p
        positivity
      have hd :
          ContinuousAt (plusWeightDerivative p) x := by
        unfold plusWeightDerivative
        exact
          ((((continuousAt_const.mul hrm).mul
            ((continuousAt_const.mul hr).add
              continuousAt_const)).neg).div
              ((hr.mul (hr.add continuousAt_const)).pow 2)
              (pow_ne_zero 2 hden0))
      exact
        (((Real.continuous_sin.comp
            (continuous_const.mul continuous_id)).div_const 2)
          |>.continuousAt.mul hd).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards with x
    have hsin :
        |Real.sin (2 * x) / 2| ≤ 1 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have h := Real.abs_sin_le_one (2 * x)
      linarith
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hsin

theorem gap11 (p : ℝ) (hp : 0 < p) :
    TailConverges (cosineCorrection p) := by
  let J : ℝ :=
    ∫ x : ℝ in Set.Ioi 2,
      (Real.sin (2 * x) / 2) *
        plusWeightDerivative p x
  let C : ℝ :=
    -(Real.sin (2 * 2) / 2 *
      positiveModelPlus p 2) - J
  have hboundary :
      Tendsto
        (fun A : ℝ =>
          (Real.sin (2 * A) / 2) *
            positiveModelPlus p A)
        atTop (𝓝 0) := by
    have hsine :
        ∀ A : ℝ, -1 / 2 ≤ Real.sin (2 * A) / 2 ∧
          Real.sin (2 * A) / 2 ≤ 1 / 2 := by
      intro A
      constructor <;>
        linarith [Real.neg_one_le_sin (2 * A),
          Real.sin_le_one (2 * A)]
    exact bdd_le_mul_tendsto_zero
      (b := (-1 / 2 : ℝ)) (B := 1 / 2)
      (Filter.Eventually.of_forall
        (fun A => (hsine A).1))
      (Filter.Eventually.of_forall
        (fun A => (hsine A).2))
      (tendsto_positiveModelPlus_atTop_zero p hp)
  have hderivIntegral :
      Tendsto
        (fun A : ℝ =>
          ∫ x in (2 : ℝ)..A,
            (Real.sin (2 * x) / 2) *
              plusWeightDerivative p x)
        atTop (𝓝 J) := by
    simpa [J] using
      (MeasureTheory.intervalIntegral_tendsto_integral_Ioi
        2
        (sine_two_mul_plusWeightDerivative_integrableOn_Ioi
          p hp)
        tendsto_id)
  have hparts :
      ∀ A : ℝ, 2 ≤ A →
        (∫ x in (2 : ℝ)..A,
          cosineCorrection p x) =
          (Real.sin (2 * A) / 2) *
              positiveModelPlus p A -
            (Real.sin (2 * 2) / 2) *
              positiveModelPlus p 2 -
            ∫ x in (2 : ℝ)..A,
              (Real.sin (2 * x) / 2) *
                plusWeightDerivative p x := by
    intro A hA
    have hu :
        ∀ x ∈ Set.uIcc (2 : ℝ) A,
          HasDerivAt
            (fun y : ℝ => Real.sin (2 * y) / 2)
            (Real.cos (2 * x)) x := by
      intro x hx
      convert
        (Real.hasDerivAt_sin (2 * x)).comp x
          (hasDerivAt_const x 2 |>.mul (hasDerivAt_id x))
          |>.div_const 2 using 1 <;> ring
    have hv :
        ∀ x ∈ Set.uIcc (2 : ℝ) A,
          HasDerivAt (positiveModelPlus p)
            (plusWeightDerivative p x) x := by
      intro x hx
      rw [Set.uIcc_of_le hA] at hx
      exact hasDerivAt_positiveModelPlus p x
        (by linarith [hx.1])
    have huInt :
        IntervalIntegrable
          (fun x : ℝ => Real.cos (2 * x))
          MeasureTheory.volume 2 A :=
      by
        simpa only [Function.comp_apply] using
          (Real.continuous_cos.comp
            (continuous_const.mul continuous_id)
            |>.intervalIntegrable (2 : ℝ) A)
    have hvInt :
        IntervalIntegrable
          (plusWeightDerivative p)
          MeasureTheory.volume 2 A := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hA]
      exact (plusWeightDerivative_integrableOn_Ioi p hp).mono_set
        Set.Ioc_subset_Ioi_self
    have h :=
      intervalIntegral.integral_deriv_mul_eq_sub
        hu hv huInt hvInt
    rw [intervalIntegral.integral_add
      (huInt.mul_continuousOn
        (fun x hx => (hv x hx).continuousAt.continuousWithinAt))
      (hvInt.continuousOn_mul
        (fun x hx => (hu x hx).continuousAt.continuousWithinAt))]
      at h
    have hfirst :
        (∫ x in (2 : ℝ)..A,
          Real.cos (2 * x) * positiveModelPlus p x) =
          ∫ x in (2 : ℝ)..A, cosineCorrection p x := by
      apply intervalIntegral.integral_congr
      intro x hx
      unfold cosineCorrection positiveModelPlus
      ring
    rw [hfirst] at h
    linarith
  refine ⟨C, ?_⟩
  have hlimit :=
    (hboundary.sub_const
      ((Real.sin (2 * 2) / 2) *
        positiveModelPlus p 2)).sub hderivIntegral
  have hlimit' :
      Tendsto
        (fun A : ℝ =>
          (Real.sin (2 * A) / 2) *
              positiveModelPlus p A -
            (Real.sin (2 * 2) / 2) *
              positiveModelPlus p 2 -
            ∫ x in (2 : ℝ)..A,
              (Real.sin (2 * x) / 2) *
                plusWeightDerivative p x)
        atTop (𝓝 C) := by
    simpa [C] using hlimit
  apply hlimit'.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with A hA
  exact (hparts A hA).symm

private lemma tailConverges_of_integrableOn_Ioi
    {f : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn f (Set.Ioi 2)) :
    TailConverges f := by
  refine ⟨∫ x : ℝ in Set.Ioi 2, f x, ?_⟩
  exact
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi
      2 hf tendsto_id

private lemma integrableOn_Ioi_of_tailConverges_of_nonneg
    {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici 2))
    (hnonneg : ∀ x : ℝ, 2 ≤ x → 0 ≤ f x)
    (hconv : TailConverges f) :
    MeasureTheory.IntegrableOn f (Set.Ioi 2) := by
  rcases hconv with ⟨L, hL⟩
  refine
    MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_tendsto
      L 2 ?_ tendsto_id ?_
  · intro A
    change MeasureTheory.IntegrableOn f
      (Set.Ioc 2 A)
    by_cases hA : 2 ≤ A
    · rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hA]
      apply ContinuousOn.intervalIntegrable
      exact hcont.mono (by
        intro x hx
        rw [Set.uIcc_of_le hA] at hx
        exact hx.1)
    · have hA' : A ≤ 2 := le_of_not_ge hA
      rw [Set.Ioc_eq_empty (not_lt_of_ge hA')]
      exact MeasureTheory.integrableOn_empty
  · apply hL.congr'
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with A hA
    symm
    apply intervalIntegral.integral_congr
    intro x hx
    change x ∈ Set.uIcc (2 : ℝ) A at hx
    rw [Set.uIcc_of_le hA] at hx
    dsimp
    rw [abs_of_nonneg (hnonneg x hx.1)]

private lemma continuousOn_positiveModelPlus_Ici
    (p : ℝ) :
    ContinuousOn (positiveModelPlus p) (Set.Ici 2) := by
  intro x hx
  have hx2 : 2 ≤ x := hx
  have hxpos : 0 < x := by linarith
  have hr :
      ContinuousAt (fun y : ℝ => Real.rpow y p) x :=
    Real.continuousAt_rpow_const x p (Or.inl hxpos.ne')
  have hden0 :
      Real.rpow x p *
        (Real.rpow x p + 1) ≠ 0 := by
    have hrpos := Real.rpow_pos_of_pos hxpos p
    positivity
  unfold positiveModelPlus
  exact
    (continuousAt_const.div
      (hr.mul (hr.add continuousAt_const))
      hden0).continuousWithinAt

private lemma positiveModelPlus_nonneg
    (p x : ℝ) (hx : 2 ≤ x) :
    0 ≤ positiveModelPlus p x := by
  have hxpos : 0 < x := by linarith
  have hrpos :
      0 < Real.rpow x p :=
    Real.rpow_pos_of_pos hxpos p
  unfold positiveModelPlus
  exact div_nonneg zero_le_one
    (mul_nonneg hrpos.le (by positivity))

private lemma rpow_neg_two_mul_le_twice_positiveModelPlus
    (p x : ℝ) (hp : 0 < p) (hx : 2 ≤ x) :
    Real.rpow x (-2 * p) ≤
      2 * positiveModelPlus p x := by
  let r : ℝ := Real.rpow x p
  have hxpos : 0 < x := by linarith
  have hrgt : 1 < r := by
    dsimp [r]
    exact Real.one_lt_rpow
      (one_lt_two.trans_le hx) hp
  have hrpos : 0 < r := zero_lt_one.trans hrgt
  have hneg :
      Real.rpow x (-p) = r⁻¹ := by
    dsimp [r]
    simpa only using Real.rpow_neg hxpos.le p
  have htwo :
      Real.rpow x (-2 * p) =
        Real.rpow x (-p) * Real.rpow x (-p) := by
    calc
      Real.rpow x (-2 * p) =
          Real.rpow x ((-p) + (-p)) := by ring
      _ = _ := Real.rpow_add hxpos (-p) (-p)
  rw [htwo, hneg]
  unfold positiveModelPlus
  change r⁻¹ * r⁻¹ ≤
    2 * (1 / (r * (r + 1)))
  field_simp [hrpos.ne']
  nlinarith

theorem gap12 (p : ℝ) (hp : 0 < p) (hpcrit : p ≤ 1 / 2) :
    ¬ TailConverges (positiveModelPlus p) := by
  intro htail
  have hplus :
      MeasureTheory.IntegrableOn
        (positiveModelPlus p) (Set.Ioi 2) :=
    integrableOn_Ioi_of_tailConverges_of_nonneg
      (continuousOn_positiveModelPlus_Ici p)
      (positiveModelPlus_nonneg p) htail
  have hmajor := hplus.const_mul 2
  have hpow :
      MeasureTheory.IntegrableOn
        (fun x : ℝ => Real.rpow x (-2 * p))
        (Set.Ioi 2) := by
    refine hmajor.mono' ?_ ?_
    · have hcont :
          ContinuousOn
            (fun x : ℝ => Real.rpow x (-2 * p))
            (Set.Ioi 2) := by
        intro x hx
        have hx2 : 2 < x := hx
        exact
          (Real.continuousAt_rpow_const x (-2 * p)
            (Or.inl (by linarith))).continuousWithinAt
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
        with x hx
      have hx2 : 2 < x := hx
      have hnonneg :
          0 ≤ Real.rpow x (-2 * p) :=
        Real.rpow_nonneg (by linarith) _
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact
        rpow_neg_two_mul_le_twice_positiveModelPlus
          p x hp hx.le
  have hexp :
      -2 * p < -1 :=
    (integrableOn_Ioi_rpow_iff
      (by norm_num : (0 : ℝ) < 2)).mp hpow
  linarith

private lemma continuousOn_positiveModelMinus_Ici
    (p : ℝ) (hp : 0 < p) :
    ContinuousOn (positiveModelMinus p) (Set.Ici 2) := by
  intro x hx
  have hx2 : 2 ≤ x := hx
  have hxpos : 0 < x := by linarith
  have hr :
      ContinuousAt (fun y : ℝ => Real.rpow y p) x :=
    Real.continuousAt_rpow_const x p (Or.inl hxpos.ne')
  have hrgt :
      1 < Real.rpow x p :=
    rpow_gt_one_on_tail p x hp hx2
  have hden0 :
      Real.rpow x p *
        (Real.rpow x p - 1) ≠ 0 := by
    exact mul_ne_zero
      (ne_of_gt (zero_lt_one.trans hrgt))
      (sub_ne_zero.mpr (ne_of_gt hrgt))
  unfold positiveModelMinus
  exact
    (continuousAt_const.div
      (hr.mul (hr.sub continuousAt_const))
      hden0).continuousWithinAt

private lemma positiveModelMinus_le_const_rpow
    (p x : ℝ) (hp : 0 < p) (hx : 2 ≤ x) :
    positiveModelMinus p x ≤
      (Real.rpow 2 p / (Real.rpow 2 p - 1)) *
        Real.rpow x (-2 * p) := by
  let q : ℝ := Real.rpow 2 p
  let r : ℝ := Real.rpow x p
  have hqgt : 1 < q := by
    dsimp [q]
    exact Real.one_lt_rpow one_lt_two hp
  have hrgt : 1 < r := by
    dsimp [r]
    exact rpow_gt_one_on_tail p x hp hx
  have hqr : q ≤ r := by
    dsimp [q, r]
    exact Real.rpow_le_rpow
      (by norm_num) hx hp.le
  have hxpos : 0 < x := by linarith
  have hrpos : 0 < r := zero_lt_one.trans hrgt
  have hratio :
      r / (r - 1) ≤ q / (q - 1) := by
    apply (div_le_div_iff₀
      (sub_pos.mpr hrgt) (sub_pos.mpr hqgt)).2
    nlinarith
  have hneg :
      Real.rpow x (-p) = r⁻¹ := by
    dsimp [r]
    simpa only using Real.rpow_neg hxpos.le p
  have htwo :
      Real.rpow x (-2 * p) =
        Real.rpow x (-p) * Real.rpow x (-p) := by
    calc
      Real.rpow x (-2 * p) =
          Real.rpow x ((-p) + (-p)) := by ring
      _ = _ := Real.rpow_add hxpos (-p) (-p)
  rw [htwo, hneg]
  unfold positiveModelMinus
  change 1 / (r * (r - 1)) ≤
    (q / (q - 1)) * (r⁻¹ * r⁻¹)
  field_simp [hrpos.ne', ne_of_gt (sub_pos.mpr hrgt),
    ne_of_gt (sub_pos.mpr hqgt)]
  exact hratio

theorem gap13 (p : ℝ) (hpcrit : 1 / 2 < p) :
    TailConverges (positiveModelMinus p) := by
  have hp : 0 < p := by linarith
  have hexp : -2 * p < -1 := by linarith
  have hpow :
      MeasureTheory.IntegrableOn
        (fun x : ℝ => Real.rpow x (-2 * p))
        (Set.Ioi 2) :=
    integrableOn_Ioi_rpow_of_lt hexp (by norm_num)
  let C : ℝ :=
    Real.rpow 2 p / (Real.rpow 2 p - 1)
  have hCpos : 0 < C := by
    dsimp [C]
    have hqgt :
        1 < Real.rpow 2 p :=
      Real.one_lt_rpow one_lt_two hp
    exact div_pos (zero_lt_one.trans hqgt)
      (sub_pos.mpr hqgt)
  have hmajor := hpow.const_mul C
  have hminus :
      MeasureTheory.IntegrableOn
        (positiveModelMinus p) (Set.Ioi 2) := by
    refine hmajor.mono' ?_ ?_
    · exact
        (continuousOn_positiveModelMinus_Ici p hp
          |>.mono Set.Ioi_subset_Ici_self
          |>.aestronglyMeasurable measurableSet_Ioi)
    · filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
        with x hx
      have hx2 : 2 < x := hx
      have hnonneg :=
        gap10 p x hp hx.le
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      change positiveModelMinus p x ≤
        C * Real.rpow x (-2 * p)
      exact positiveModelMinus_le_const_rpow
        p x hp hx.le
  exact tailConverges_of_integrableOn_Ioi hminus

private lemma remainder_nonneg
    (p x : ℝ) (hp : 0 < p) (hx : 2 ≤ x) :
    0 ≤ remainder p x := by
  have hrgt :
      1 < Real.rpow x p :=
    rpow_gt_one_on_tail p x hp hx
  have hsum :
      0 < Real.rpow x p + Real.sin x := by
    linarith [Real.neg_one_le_sin x]
  unfold remainder
  exact div_nonneg (sq_nonneg _)
    (mul_nonneg (zero_lt_one.trans hrgt).le hsum.le)

private lemma continuousOn_remainder_Ici
    (p : ℝ) (hp : 0 < p) :
    ContinuousOn (remainder p) (Set.Ici 2) := by
  intro x hx
  have hx2 : 2 ≤ x := hx
  have hxpos : 0 < x := by linarith
  have hr :
      ContinuousAt (fun y : ℝ => Real.rpow y p) x :=
    Real.continuousAt_rpow_const x p (Or.inl hxpos.ne')
  have hs : ContinuousAt Real.sin x :=
    Real.continuous_sin.continuousAt
  have hrgt :
      1 < Real.rpow x p :=
    rpow_gt_one_on_tail p x hp hx2
  have hsum :
      0 < Real.rpow x p + Real.sin x := by
    linarith [Real.neg_one_le_sin x]
  have hden0 :
      Real.rpow x p *
        (Real.rpow x p + Real.sin x) ≠ 0 :=
    mul_ne_zero (ne_of_gt (zero_lt_one.trans hrgt))
      hsum.ne'
  unfold remainder
  exact
    ((hs.pow 2).div
      (hr.mul (hr.add hs))
      hden0).continuousWithinAt

theorem gap14 (p : ℝ) (hpcrit : 1 / 2 < p) :
    TailConverges (remainder p) := by
  have hp : 0 < p := by linarith
  have hminus :
      MeasureTheory.IntegrableOn
        (positiveModelMinus p) (Set.Ioi 2) :=
    integrableOn_Ioi_of_tailConverges_of_nonneg
      (continuousOn_positiveModelMinus_Ici p hp)
      (fun x hx => gap10 p x hp hx)
      (gap13 p hpcrit)
  have hrem :
      MeasureTheory.IntegrableOn
        (remainder p) (Set.Ioi 2) := by
    refine hminus.mono' ?_ ?_
    · exact
        (continuousOn_remainder_Ici p hp
          |>.mono Set.Ioi_subset_Ici_self
          |>.aestronglyMeasurable measurableSet_Ioi)
    · filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
        with x hx
      have hx2 : 2 < x := hx
      rw [Real.norm_eq_abs,
        abs_of_nonneg (remainder_nonneg p x hp hx.le)]
      exact (gap8 p x hp hx.le).trans
        (gap9 p x hp hx.le)
  exact tailConverges_of_integrableOn_Ioi hrem

private lemma continuousOn_cosineCorrection_Ici
    (p : ℝ) :
    ContinuousOn (cosineCorrection p) (Set.Ici 2) := by
  intro x hx
  have hx2 : 2 ≤ x := hx
  have hxpos : 0 < x := by linarith
  have hr :
      ContinuousAt (fun y : ℝ => Real.rpow y p) x :=
    Real.continuousAt_rpow_const x p (Or.inl hxpos.ne')
  have hden0 :
      Real.rpow x p *
        (Real.rpow x p + 1) ≠ 0 := by
    have hrpos := Real.rpow_pos_of_pos hxpos p
    exact mul_ne_zero hrpos.ne'
      (ne_of_gt (by positivity))
  unfold cosineCorrection
  exact
    ((Real.continuous_cos.comp
      (continuous_const.mul continuous_id)
      |>.continuousAt).div
        (hr.mul (hr.add continuousAt_const))
        hden0).continuousWithinAt

theorem gap15 (p : ℝ) (hp : 0 < p) (hpcrit : p ≤ 1 / 2) :
    ¬ TailConverges (remainder p) := by
  intro hremTail
  have hrem :
      MeasureTheory.IntegrableOn
        (remainder p) (Set.Ioi 2) :=
    integrableOn_Ioi_of_tailConverges_of_nonneg
      (continuousOn_remainder_Ici p hp)
      (fun x hx => remainder_nonneg p x hp hx)
      hremTail
  let q : ℝ → ℝ :=
    fun x =>
      (1 / 2 : ℝ) *
        (positiveModelPlus p x -
          cosineCorrection p x)
  have hqcont :
      ContinuousOn q (Set.Ici 2) := by
    dsimp [q]
    exact continuousOn_const.mul
      ((continuousOn_positiveModelPlus_Ici p).sub
        (continuousOn_cosineCorrection_Ici p))
  have hq :
      MeasureTheory.IntegrableOn q (Set.Ioi 2) := by
    refine hrem.mono' ?_ ?_
    · exact
        (hqcont.mono Set.Ioi_subset_Ici_self
          |>.aestronglyMeasurable measurableSet_Ioi)
    · filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
        with x hx
      have hx2 : 2 < x := hx
      have hqnonneg : 0 ≤ q x := by
        exact gap5 p x hp hx.le
      rw [Real.norm_eq_abs, abs_of_nonneg hqnonneg]
      change
        (1 / 2 : ℝ) *
            (positiveModelPlus p x -
              cosineCorrection p x) ≤
          remainder p x
      rw [gap6 p x hp hx.le]
      exact gap7 p x hp hx.le
  have htwoq :
      MeasureTheory.IntegrableOn
        (fun x : ℝ => 2 * q x) (Set.Ioi 2) :=
    hq.const_mul 2
  rcases tailConverges_of_integrableOn_Ioi htwoq with
    ⟨Lq, hLq⟩
  rcases gap11 p hp with ⟨Lc, hLc⟩
  have hsum :
      Tendsto
        (fun A : ℝ =>
          (∫ x in (2 : ℝ)..A, 2 * q x) +
            ∫ x in (2 : ℝ)..A,
              cosineCorrection p x)
        atTop (𝓝 (Lq + Lc)) :=
    hLq.add hLc
  have hplusTail :
      TailConverges (positiveModelPlus p) := by
    refine ⟨Lq + Lc, ?_⟩
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop (2 : ℝ)]
      with A hA
    have hqInt :
        IntervalIntegrable
          (fun x : ℝ => 2 * q x)
          MeasureTheory.volume 2 A := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hA]
      exact htwoq.mono_set Set.Ioc_subset_Ioi_self
    have hcInt :
        IntervalIntegrable
          (cosineCorrection p)
          MeasureTheory.volume 2 A := by
      apply ContinuousOn.intervalIntegrable
      exact (continuousOn_cosineCorrection_Ici p).mono
        (by
          intro x hx
          rw [Set.uIcc_of_le hA] at hx
          exact hx.1)
    rw [← intervalIntegral.integral_add hqInt hcInt]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [q]
    ring
  exact (gap12 p hp hpcrit) hplusTail

private lemma integrand_denominator_pos
    (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    0 < Real.rpow x p + Real.sin x := by
  by_cases hx1 : x ≤ 1
  · have hsinpos : 0 < Real.sin x :=
      Real.sin_pos_of_pos_of_lt_pi hx
        (hx1.trans_lt
          (lt_of_lt_of_le one_lt_two Real.two_le_pi))
    have hrnonneg :
        0 ≤ Real.rpow x p :=
      Real.rpow_nonneg hx.le _
    linarith
  · have hxgt : 1 < x := lt_of_not_ge hx1
    have hrgt : 1 < Real.rpow x p :=
      Real.one_lt_rpow hxgt hp
    linarith [Real.neg_one_le_sin x]

private lemma continuousOn_integrand_Ioi
    (p : ℝ) (hp : 0 < p) :
    ContinuousOn (integrand p) (Set.Ioi 0) := by
  intro x hx
  have hxpos : 0 < x := hx
  have hr :
      ContinuousAt (fun y : ℝ => Real.rpow y p) x :=
    Real.continuousAt_rpow_const x p (Or.inl hxpos.ne')
  have hs : ContinuousAt Real.sin x :=
    Real.continuous_sin.continuousAt
  have hden0 :
      Real.rpow x p + Real.sin x ≠ 0 :=
    (integrand_denominator_pos p x hp hxpos).ne'
  unfold integrand
  exact
    (hs.div (hr.add hs) hden0).continuousWithinAt

private lemma integrand_intervalIntegrable_zero
    (p A : ℝ) (hp : 0 < p) (hA : 0 < A) :
    IntervalIntegrable (integrand p)
      MeasureTheory.volume 0 A := by
  let g : ℝ → ℝ :=
    Function.update (integrand p) 0
      (rightLimitValue p)
  have hgcont :
      ContinuousOn g (Set.Icc 0 A) := by
    dsimp [g]
    rw [continuousOn_update_iff]
    constructor
    · exact (continuousOn_integrand_Ioi p hp).mono
        (by
          intro x hx
          have hx0 : x ≠ 0 := by
            simpa only [Set.mem_singleton_iff] using hx.2
          exact lt_of_le_of_ne hx.1.1 (Ne.symm hx0))
    · intro hzero
      apply (gap1 p hp).mono_left
      exact nhdsWithin_mono 0
        (by
          intro x hx
          have hx0 : x ≠ 0 := by
            simpa only [Set.mem_singleton_iff] using hx.2
          exact lt_of_le_of_ne hx.1.1 (Ne.symm hx0))
  have hgInt :
      IntervalIntegrable g MeasureTheory.volume 0 A :=
    by
      apply ContinuousOn.intervalIntegrable
      simpa only [Set.uIcc_of_le hA.le] using hgcont
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hA.le]
    at hgInt ⊢
  exact hgInt.congr_fun
    (by
      intro x hx
      dsimp [g]
      rw [Function.update_of_ne (ne_of_gt hx.1)])
    measurableSet_Ioc

private lemma continuousOn_sineModel_Ici
    (p : ℝ) :
    ContinuousOn (sineModel p) (Set.Ici 2) := by
  intro x hx
  have hx2 : 2 ≤ x := hx
  have hxpos : 0 < x := by linarith
  have hr :
      ContinuousAt (fun y : ℝ => Real.rpow y p) x :=
    Real.continuousAt_rpow_const x p (Or.inl hxpos.ne')
  have hrpos :
      0 < Real.rpow x p :=
    Real.rpow_pos_of_pos hxpos p
  unfold sineModel
  exact
    (Real.continuous_sin.continuousAt.div
      hr hrpos.ne').continuousWithinAt

theorem gap16 (p : ℝ) (hp : 0 < p) :
    1 / 2 < p ↔ Converges p := by
  constructor
  · intro hpcrit
    have hlocal :
        ∀ A : ℝ, 0 < A →
          IntervalIntegrable (integrand p)
            MeasureTheory.volume 0 A :=
      fun A hA =>
        integrand_intervalIntegrable_zero p A hp hA
    have hintegrandTail :
        TailConverges (integrand p) := by
      rcases gap4 p hp with ⟨Ls, hLs⟩
      rcases gap14 p hpcrit with ⟨Lr, hLr⟩
      refine ⟨Ls - Lr, ?_⟩
      have hdiff :
          Tendsto
            (fun A : ℝ =>
              (∫ x in (2 : ℝ)..A,
                sineModel p x) -
              ∫ x in (2 : ℝ)..A,
                remainder p x)
            atTop (𝓝 (Ls - Lr)) :=
        hLs.sub hLr
      apply hdiff.congr'
      filter_upwards [eventually_ge_atTop (2 : ℝ)]
        with A hA
      have hsInt :
          IntervalIntegrable (sineModel p)
            MeasureTheory.volume 2 A := by
        apply ContinuousOn.intervalIntegrable
        exact (continuousOn_sineModel_Ici p).mono
          (by
            intro x hx
            rw [Set.uIcc_of_le hA] at hx
            exact hx.1)
      have hrInt :
          IntervalIntegrable (remainder p)
            MeasureTheory.volume 2 A := by
        apply ContinuousOn.intervalIntegrable
        exact (continuousOn_remainder_Ici p hp).mono
          (by
            intro x hx
            rw [Set.uIcc_of_le hA] at hx
            exact hx.1)
      rw [← intervalIntegral.integral_sub hsInt hrInt]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hA] at hx
      exact (gap3 p x hp (by linarith [hx.1])).symm
    constructor
    · exact hlocal
    · rcases hintegrandTail with ⟨Lt, hLt⟩
      let K : ℝ :=
        ∫ x in (0 : ℝ)..2, integrand p x
      refine ⟨K + Lt, ?_⟩
      have hsum :
          Tendsto
            (fun A : ℝ =>
              K + ∫ x in (2 : ℝ)..A,
                integrand p x)
            atTop (𝓝 (K + Lt)) :=
        tendsto_const_nhds.add hLt
      apply hsum.congr'
      filter_upwards [eventually_ge_atTop (2 : ℝ)]
        with A hA
      have h02 :
          IntervalIntegrable (integrand p)
            MeasureTheory.volume 0 2 :=
        hlocal 2 (by norm_num)
      have h2A :
          IntervalIntegrable (integrand p)
            MeasureTheory.volume 2 A := by
        apply ContinuousOn.intervalIntegrable
        exact (continuousOn_integrand_Ioi p hp).mono
          (by
            intro x hx
            rw [Set.uIcc_of_le hA] at hx
            exact lt_of_lt_of_le (by norm_num) hx.1)
      have hadj :=
        intervalIntegral.integral_add_adjacent_intervals
          h02 h2A
      simpa [K, partialIntegral] using hadj
  · intro hconv
    rcases hconv with ⟨hlocal, L, hL⟩
    by_contra hpcritNeg
    have hpcrit : p ≤ 1 / 2 :=
      le_of_not_gt hpcritNeg
    have hintegrandTail :
        TailConverges (integrand p) := by
      let K : ℝ :=
        ∫ x in (0 : ℝ)..2, integrand p x
      refine ⟨L - K, ?_⟩
      have hdiff :
          Tendsto
            (fun A : ℝ => partialIntegral p A - K)
            atTop (𝓝 (L - K)) :=
        hL.sub_const K
      apply hdiff.congr'
      filter_upwards [eventually_ge_atTop (2 : ℝ)]
        with A hA
      have h02 :
          IntervalIntegrable (integrand p)
            MeasureTheory.volume 0 2 :=
        hlocal 2 (by norm_num)
      have h2A :
          IntervalIntegrable (integrand p)
            MeasureTheory.volume 2 A := by
        apply ContinuousOn.intervalIntegrable
        exact (continuousOn_integrand_Ioi p hp).mono
          (by
            intro x hx
            rw [Set.uIcc_of_le hA] at hx
            exact lt_of_lt_of_le (by norm_num) hx.1)
      have hadj :=
        intervalIntegral.integral_add_adjacent_intervals
          h02 h2A
      unfold partialIntegral
      dsimp [K]
      linarith
    have hremainderTail :
        TailConverges (remainder p) := by
      rcases gap4 p hp with ⟨Ls, hLs⟩
      rcases hintegrandTail with ⟨Li, hLi⟩
      refine ⟨Ls - Li, ?_⟩
      have hdiff :
          Tendsto
            (fun A : ℝ =>
              (∫ x in (2 : ℝ)..A,
                sineModel p x) -
              ∫ x in (2 : ℝ)..A,
                integrand p x)
            atTop (𝓝 (Ls - Li)) :=
        hLs.sub hLi
      apply hdiff.congr'
      filter_upwards [eventually_ge_atTop (2 : ℝ)]
        with A hA
      have hsInt :
          IntervalIntegrable (sineModel p)
            MeasureTheory.volume 2 A := by
        apply ContinuousOn.intervalIntegrable
        exact (continuousOn_sineModel_Ici p).mono
          (by
            intro x hx
            rw [Set.uIcc_of_le hA] at hx
            exact hx.1)
      have hiInt :
          IntervalIntegrable (integrand p)
            MeasureTheory.volume 2 A := by
        apply ContinuousOn.intervalIntegrable
        exact (continuousOn_integrand_Ioi p hp).mono
          (by
            intro x hx
            rw [Set.uIcc_of_le hA] at hx
            exact lt_of_lt_of_le (by norm_num) hx.1)
      rw [← intervalIntegral.integral_sub hsInt hiInt]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hA] at hx
      have hid :=
        gap3 p x hp (by linarith [hx.1])
      linarith
    exact (gap15 p hp hpcrit) hremainderTail

end

end ProofGap.Exercise3748
