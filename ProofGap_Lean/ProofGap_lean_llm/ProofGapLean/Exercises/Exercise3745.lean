import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Set
open scoped Interval Topology

noncomputable section

private lemma rem_integrable (α : ℝ) (hα : 0 < α) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => (-α * Real.rpow x (-α - 1)) * Real.sin x)
      (Set.Ioi 1) := by
  have hbase :
      MeasureTheory.IntegrableOn (fun x : ℝ => Real.rpow x (-α - 1))
        (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  refine (hbase.const_mul |α|).mono' ?_ ?_
  · have hrpow :
        ContinuousOn (fun x : ℝ => Real.rpow x (-α - 1)) (Set.Ioi 1) :=
      fun x hx =>
        (Real.continuousAt_rpow_const x (-α - 1)
          (Or.inl (ne_of_gt (lt_trans zero_lt_one hx)))).continuousWithinAt
    exact ((continuousOn_const.mul hrpow).mul
      Real.continuous_sin.continuousOn).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := (lt_trans zero_lt_one hx).le
    simp only [Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_neg]
    calc
      |α| * |Real.rpow x (-α - 1)| * |Real.sin x| ≤
          |α| * |Real.rpow x (-α - 1)| * 1 := by
        gcongr
        exact Real.abs_sin_le_one x
      _ = |α| * Real.rpow x (-α - 1) := by
        have hrabs :
            |Real.rpow x (-α - 1)| = Real.rpow x (-α - 1) :=
          abs_of_nonneg (Real.rpow_nonneg hx0 _)
        rw [hrabs, mul_one]

private lemma boundary_tendsto (α : ℝ) (hα : 0 < α) :
    Tendsto (fun x : ℝ => Real.rpow x (-α) * Real.sin x)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hp := (tendsto_rpow_neg_atTop hα)
  rw [Metric.tendsto_nhds] at hp
  filter_upwards [hp ε hε, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [Real.dist_eq, sub_zero, abs_mul]
  have hr0 : 0 ≤ Real.rpow x (-α) := Real.rpow_nonneg hx0 _
  rw [Real.dist_eq, sub_zero] at hx
  change |Real.rpow x (-α)| < ε at hx
  rw [abs_of_nonneg hr0] at hx
  rw [abs_of_nonneg hr0]
  calc
    Real.rpow x (-α) * |Real.sin x| ≤ Real.rpow x (-α) * 1 := by
      gcongr
      exact Real.abs_sin_le_one x
    _ = Real.rpow x (-α) := mul_one _
    _ < ε := hx

private lemma ibp_formula (α B : ℝ) (_hα : 0 < α) (hB : 1 ≤ B) :
    (∫ x in (1 : ℝ)..B,
        Real.rpow x (-α) * Real.cos x) =
      Real.rpow B (-α) * Real.sin B -
        Real.rpow 1 (-α) * Real.sin 1 -
        ∫ x in (1 : ℝ)..B,
          (-α * Real.rpow x (-α - 1)) * Real.sin x := by
  have hu : ∀ x ∈ Set.uIcc (1 : ℝ) B,
      HasDerivAt
        (fun t : ℝ => Real.rpow t (-α))
        (-α * Real.rpow x (-α - 1)) x := by
    intro x hx
    rw [Set.uIcc_of_le hB] at hx
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans_le hx.1)
    convert Real.hasDerivAt_rpow_const (x := x) (p := -α)
      (Or.inl hx0) using 1 <;> ring
  have hv : ∀ x ∈ Set.uIcc (1 : ℝ) B,
      HasDerivAt Real.sin (Real.cos x) x :=
    fun x hx => Real.hasDerivAt_sin x
  have hu' :
      IntervalIntegrable
        (fun x : ℝ => -α * Real.rpow x (-α - 1))
        MeasureTheory.volume 1 B := by
    have hrpow :
        ContinuousOn (fun x : ℝ => Real.rpow x (-α - 1))
          (Set.uIcc (1 : ℝ) B) := by
      intro x hx
      rw [Set.uIcc_of_le hB] at hx
      exact (Real.continuousAt_rpow_const x (-α - 1)
        (Or.inl (ne_of_gt (zero_lt_one.trans_le hx.1)))).continuousWithinAt
    exact (continuousOn_const.mul hrpow).intervalIntegrable
  have hv' :
      IntervalIntegrable Real.cos MeasureTheory.volume 1 B :=
    Real.continuous_cos.intervalIntegrable _ _
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hu hv hu' hv'

private lemma aux_model_converges (α : ℝ) (hα : 0 < α) :
    ∃ L : ℝ,
      Tendsto
        (fun A : ℝ =>
          ∫ t in (1 : ℝ)..A,
            Real.rpow t (-α) * Real.cos t)
        atTop (𝓝 L) := by
  let R : ℝ :=
    ∫ x : ℝ in Set.Ioi 1,
      (-α * Real.rpow x (-α - 1)) * Real.sin x
  refine ⟨0 - Real.rpow 1 (-α) * Real.sin 1 - R, ?_⟩
  have hb := boundary_tendsto α hα
  have hr :
      Tendsto
        (fun A : ℝ =>
          ∫ x in (1 : ℝ)..A,
            (-α * Real.rpow x (-α - 1)) * Real.sin x)
        atTop (𝓝 R) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi
      1 (rem_integrable α hα) tendsto_id
  have hlim :=
    (hb.sub_const (Real.rpow 1 (-α) * Real.sin 1)).sub hr
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with A hA
  exact (ibp_formula α A hα hA).symm

private lemma positive_model_converges (α : ℝ) (hα : 0 < α) :
    ∃ L : ℝ,
      Tendsto
        (fun A : ℝ =>
          ∫ t in (1 : ℝ)..A,
            Real.cos t / Real.rpow t α)
        atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := aux_model_converges α hα
  refine ⟨L, hL.congr' ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with A hA
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le hA] at hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx.1
  dsimp
  rw [Real.rpow_neg hx0]
  simp [div_eq_mul_inv, mul_comm]

private lemma not_tendsto_sin_atTop (L : ℝ) :
    ¬ Tendsto Real.sin atTop (𝓝 L) := by
  intro hL
  let s : ℕ → ℝ :=
    fun n => Real.pi / 2 + (n : ℝ) * (2 * Real.pi)
  let t : ℕ → ℝ :=
    fun n => 3 * Real.pi / 2 + (n : ℝ) * (2 * Real.pi)
  have hbase :
      Tendsto (fun n : ℕ => (n : ℝ) * (2 * Real.pi)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop
      (mul_pos two_pos Real.pi_pos)).congr (fun n => by ring)
  have hs : Tendsto s atTop atTop := by
    exact tendsto_atTop_add_const_left atTop (Real.pi / 2) hbase
  have ht : Tendsto t atTop atTop := by
    exact tendsto_atTop_add_const_left atTop (3 * Real.pi / 2) hbase
  have hLs := hL.comp hs
  have hLt := hL.comp ht
  have hsone :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 L) := by
    apply hLs.congr'
    filter_upwards [] with n
    dsimp [s]
    rw [Real.sin_add_nat_mul_two_pi]
    norm_num
  have htneg :
      Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 L) := by
    apply hLt.congr'
    filter_upwards [] with n
    dsimp [t]
    rw [Real.sin_add_nat_mul_two_pi]
    rw [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring]
    rw [Real.sin_add]
    norm_num
  have hL1 : L = 1 :=
    tendsto_nhds_unique hsone tendsto_const_nhds
  have hLn : L = -1 :=
    tendsto_nhds_unique htneg tendsto_const_nhds
  norm_num [hL1] at hLn

private lemma zero_model_not_converges :
    ¬ ∃ L : ℝ,
      Tendsto
        (fun A : ℝ =>
          ∫ t in (1 : ℝ)..A,
            Real.cos t / Real.rpow t 0)
        atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hformula :
      (fun A : ℝ =>
        ∫ t in (1 : ℝ)..A,
          Real.cos t / Real.rpow t 0) =
        fun A => Real.sin A - Real.sin 1 := by
    funext A
    change (∫ t in (1 : ℝ)..A, Real.cos t / (t ^ (0 : ℝ))) =
      Real.sin A - Real.sin 1
    simp only [Real.rpow_zero, div_one]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => Real.hasDerivAt_sin x)
      (Real.continuous_cos.intervalIntegrable _ _)]
  rw [hformula] at hL
  have hsin :
      Tendsto Real.sin atTop (𝓝 (L + Real.sin 1)) := by
    have := hL.add_const (Real.sin 1)
    convert this using 1 <;> ring
  exact not_tendsto_sin_atTop _ hsin

private lemma sqrt_two_div_two_eq_inv :
    Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  nlinarith

private lemma block_lower (β : ℝ) (hβ : 0 < β)
    (m : ℕ) (hm : 1 ≤ m) :
    (∫ t in 2 * (m : ℝ) * Real.pi..
          2 * (m : ℝ) * Real.pi + Real.pi / 4,
          Real.rpow t β * Real.cos t) >
      Real.rpow (2 * (m : ℝ) * Real.pi) β *
        (1 / Real.sqrt 2) * (Real.pi / 4) := by
  let a : ℝ := 2 * (m : ℝ) * Real.pi
  let b : ℝ := a + Real.pi / 4
  let c : ℝ := Real.rpow a β * (1 / Real.sqrt 2)
  have ha0 : 0 < a := by
    dsimp [a]
    positivity
  have hab : a < b := by
    dsimp [b]
    linarith [Real.pi_pos]
  have hcont :
      ContinuousOn
        (fun t : ℝ => Real.rpow t β * Real.cos t)
        (Set.Icc a b) := by
    have hrpow :
        ContinuousOn (fun t : ℝ => Real.rpow t β) (Set.Icc a b) :=
      fun t ht =>
        (Real.continuousAt_rpow_const t β
          (Or.inl (ne_of_gt (ha0.trans_le ht.1)))).continuousWithinAt
    exact hrpow.mul Real.continuous_cos.continuousOn
  have hle : ∀ t ∈ Set.Ioc a b,
      c ≤ Real.rpow t β * Real.cos t := by
    intro t ht
    have ht0 : 0 ≤ t := (ha0.trans ht.1).le
    have hpow :
        Real.rpow a β ≤ Real.rpow t β :=
      Real.rpow_le_rpow ha0.le ht.1.le (le_of_lt hβ)
    have hphase : Real.cos t = Real.cos (t - a) := by
      have heq :
          t = (t - a) + m * (2 * Real.pi) := by
        dsimp [a]
        push_cast
        ring
      calc
        Real.cos t =
            Real.cos ((t - a) + m * (2 * Real.pi)) :=
          congrArg Real.cos heq
        _ = Real.cos (t - a) := by
          rw [Real.cos_add_nat_mul_two_pi]
    have hu : t - a ∈ Set.Icc (0 : ℝ) (Real.pi / 4) := by
      have hta : a < t := ht.1
      have htb : t ≤ a + Real.pi / 4 := by
        simpa [b] using ht.2
      constructor <;> linarith
    have hv : Real.pi / 4 ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor <;> linarith [Real.pi_pos]
    have hu' : t - a ∈ Set.Icc (0 : ℝ) Real.pi := by
      exact ⟨hu.1, hu.2.trans hv.2⟩
    have hcos0 :
        Real.cos (Real.pi / 4) ≤ Real.cos (t - a) :=
      Real.antitoneOn_cos hu' hv hu.2
    have hcos :
        1 / Real.sqrt 2 ≤ Real.cos t := by
      rw [hphase, ← sqrt_two_div_two_eq_inv,
        ← Real.cos_pi_div_four]
      exact hcos0
    dsimp [c]
    exact mul_le_mul hpow hcos
      (by positivity) (Real.rpow_nonneg ht0 _)
  have hstrict :
      ∃ t ∈ Set.Icc a b,
        c < Real.rpow t β * Real.cos t := by
    refine ⟨a, Set.left_mem_Icc.mpr hab.le, ?_⟩
    have hcos_a : Real.cos a = 1 := by
      have heq : a = 0 + m * (2 * Real.pi) := by
        dsimp [a]
        push_cast
        ring
      rw [heq, Real.cos_add_nat_mul_two_pi, Real.cos_zero]
    have hfrac : 1 / Real.sqrt 2 < 1 := by
      exact (div_lt_one (by positivity)).mpr Real.one_lt_sqrt_two
    dsimp [c]
    rw [hcos_a]
    simpa using
      (mul_lt_mul_of_pos_left hfrac (Real.rpow_pos_of_pos ha0 β))
  have hlt :=
    intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      hab continuousOn_const hcont hle hstrict
  dsimp [a, b, c] at hlt ⊢
  rw [intervalIntegral.integral_const] at hlt
  norm_num at hlt
  simpa [mul_assoc, mul_left_comm, mul_comm] using hlt

private lemma block_lower_tendsto (β : ℝ) (hβ : 0 < β) :
    Tendsto
      (fun m : ℕ =>
        Real.rpow (2 * (m : ℝ) * Real.pi) β *
          (1 / Real.sqrt 2) * (Real.pi / 4))
      atTop atTop := by
  have hbase :
      Tendsto (fun m : ℕ => 2 * (m : ℝ) * Real.pi) atTop atTop := by
    have hmul :
        Tendsto (fun m : ℕ => (2 * Real.pi) * (m : ℝ))
          atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop
        (mul_pos two_pos Real.pi_pos)
    exact hmul.congr (fun m => by ring)
  have hr :
      Tendsto (fun m : ℕ =>
        Real.rpow (2 * (m : ℝ) * Real.pi) β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp hbase
  have hc1 : 0 < 1 / Real.sqrt 2 := by positivity
  have hc2 : 0 < Real.pi / 4 := by positivity
  have h1 := hr.const_mul_atTop hc1
  have h2 := h1.const_mul_atTop hc2
  exact h2.congr (fun m => by ring)

private lemma block_integral_tendsto (β : ℝ) (hβ : 0 < β) :
    Tendsto
      (fun m : ℕ =>
        ∫ t in 2 * (m : ℝ) * Real.pi..
          2 * (m : ℝ) * Real.pi + Real.pi / 4,
          Real.rpow t β * Real.cos t)
      atTop atTop := by
  apply tendsto_atTop_mono (fun m => ?_) (block_lower_tendsto β hβ)
  by_cases hm : 1 ≤ m
  · exact (block_lower β hβ m hm).le
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    have hz : Real.rpow 0 β = 0 := by
      change (0 : ℝ) ^ β = 0
      exact Real.zero_rpow hβ.ne'
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add]
    rw [hz, zero_mul]
    simp only [zero_mul]
    apply intervalIntegral.integral_nonneg (by positivity)
    intro t ht
    exact mul_nonneg
      (Real.rpow_nonneg ht.1 _)
      (Real.cos_nonneg_of_mem_Icc
        ⟨(neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans ht.1,
          ht.2.trans (by linarith [Real.pi_pos])⟩)

private lemma negative_model_not_converges (β : ℝ) (hβ : 0 < β) :
    ¬ ∃ L : ℝ,
      Tendsto
        (fun A : ℝ =>
          ∫ t in (1 : ℝ)..A,
            Real.cos t / Real.rpow t (-β))
        atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  let f : ℝ → ℝ := fun t => Real.rpow t β * Real.cos t
  have hF :
      Tendsto (fun A : ℝ => ∫ t in (1 : ℝ)..A, f t)
        atTop (𝓝 L) := by
    apply hL.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with A hA
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hA] at ht
    have ht0 : 0 ≤ t := zero_le_one.trans ht.1
    dsimp [f]
    rw [Real.rpow_neg ht0]
    field_simp
  let a : ℕ → ℝ := fun m => 2 * (m : ℝ) * Real.pi
  let b : ℕ → ℝ := fun m => a m + Real.pi / 4
  have ha : Tendsto a atTop atTop := by
    have hmul :
        Tendsto (fun m : ℕ => (2 * Real.pi) * (m : ℝ))
          atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop
        (mul_pos two_pos Real.pi_pos)
    exact hmul.congr (fun m => by
      dsimp [a]
      ring)
  have hb : Tendsto b atTop atTop := by
    exact tendsto_atTop_add_const_right atTop (Real.pi / 4) ha
  have hFa := hF.comp ha
  have hFb := hF.comp hb
  have hzero :
      Tendsto
        (fun m : ℕ => ∫ t in a m..b m, f t)
        atTop (𝓝 0) := by
    have hdiff :
        Tendsto
          (fun m : ℕ =>
            (∫ t in (1 : ℝ)..b m, f t) -
              ∫ t in (1 : ℝ)..a m, f t)
          atTop (𝓝 0) := by
      simpa using hFb.sub hFa
    apply hdiff.congr'
    filter_upwards [] with m
    have hint₁ :
        IntervalIntegrable f MeasureTheory.volume 1 (a m) := by
      have hcont : Continuous f := by
        apply Continuous.mul
        · exact Real.continuous_rpow_const hβ.le
        · exact Real.continuous_cos
      exact hcont.intervalIntegrable _ _
    have hint₂ :
        IntervalIntegrable f MeasureTheory.volume (a m) (b m) := by
      have ham0 : 0 ≤ a m := by
        dsimp [a]
        positivity
      have hrpow :
          ContinuousOn (fun t : ℝ => Real.rpow t β)
            (Set.uIcc (a m) (b m)) := by
        intro t ht
        exact (Real.continuousAt_rpow_const t β
          (Or.inr (le_of_lt hβ))).continuousWithinAt
      exact (hrpow.mul Real.continuous_cos.continuousOn).intervalIntegrable
    have hadd :=
      intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂
    rw [← hadd]
    ring
  have htop :
      Tendsto
        (fun m : ℕ => ∫ t in a m..b m, f t)
        atTop atTop := by
    convert block_integral_tendsto β hβ using 1
  exact not_tendsto_nhds_of_tendsto_atTop htop 0 hzero

private lemma model_converges_iff_raw (α : ℝ) :
    (∃ L : ℝ,
      Tendsto
        (fun A : ℝ =>
          ∫ t in (1 : ℝ)..A,
            Real.cos t / Real.rpow t α)
        atTop (𝓝 L)) ↔
      0 < α := by
  constructor
  · intro hconv
    by_contra hnot
    have hle : α ≤ 0 := le_of_not_gt hnot
    rcases hle.eq_or_lt with hzero | hneg
    · subst α
      exact zero_model_not_converges hconv
    · have hβ : 0 < -α := neg_pos.mpr hneg
      have hbad := negative_model_not_converges (-α) hβ
      apply hbad
      simpa using hconv
  · exact positive_model_converges α

private lemma reciprocal_one_sub_tendsto :
    Tendsto (fun A : ℝ => 1 / (1 - A))
      (𝓝[<] (1 : ℝ)) atTop := by
  have hsub :
      Tendsto (fun A : ℝ => 1 - A)
        (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hid :
          Tendsto (fun A : ℝ => A) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
        tendsto_nhds_of_tendsto_nhdsWithin tendsto_id
      simpa using
        (tendsto_const_nhds (x := (1 : ℝ))).sub hid
    · filter_upwards [self_mem_nhdsWithin] with A hA
      exact sub_pos.mpr (show A < 1 from hA)
  simpa only [one_div] using tendsto_inv_nhdsGT_zero.comp hsub

private lemma one_sub_reciprocal_tendsto :
    Tendsto (fun T : ℝ => 1 - 1 / T)
      atTop (𝓝[<] (1 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hinv :
        Tendsto (fun T : ℝ => 1 / T) atTop (𝓝 0) := by
      simpa [one_div] using
        (tendsto_inv_atTop_zero : Tendsto (fun T : ℝ => T⁻¹)
          atTop (𝓝 0))
    simpa using tendsto_const_nhds.sub hinv
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    simp only [Set.mem_Iio]
    have hinv : 0 < 1 / T := one_div_pos.mpr hT
    linarith

private lemma singular_integral_substitution
    (n A : ℝ) (hA0 : 0 ≤ A) (hA1 : A < 1) :
    (∫ x in (0 : ℝ)..A,
        Real.cos (1 / (1 - x)) /
          Real.rpow (1 - x) (1 / n)) =
      ∫ t in (1 : ℝ)..(1 / (1 - A)),
        Real.cos t / Real.rpow t (2 - 1 / n) := by
  let φ : ℝ → ℝ := fun x => (1 - x)⁻¹
  let φ' : ℝ → ℝ := fun x => ((1 - x) ^ 2)⁻¹
  let g : ℝ → ℝ :=
    fun t => Real.cos t / Real.rpow t (2 - 1 / n)
  have hφ : ∀ x ∈ Set.uIcc (0 : ℝ) A,
      HasDerivAt φ (φ' x) x := by
    intro x hx
    rw [Set.uIcc_of_le hA0] at hx
    have hx1 : x < 1 := hx.2.trans_lt hA1
    have hden : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
    have hraw := ((hasDerivAt_const x (1 : ℝ)).sub
      (hasDerivAt_id x)).inv hden
    simpa [φ, φ', one_div] using hraw
  have hφ' : ContinuousOn φ' (Set.uIcc (0 : ℝ) A) := by
    intro x hx
    rw [Set.uIcc_of_le hA0] at hx
    have hx1 : x < 1 := hx.2.trans_lt hA1
    have hden : (1 - x) ^ 2 ≠ 0 := pow_ne_zero 2
      (ne_of_gt (sub_pos.mpr hx1))
    dsimp [φ']
    exact (((continuousAt_const.sub continuousAt_id).pow 2).inv₀
      hden).continuousWithinAt
  have hg : ContinuousOn g (φ '' Set.uIcc (0 : ℝ) A) := by
    rintro t ⟨x, hx, rfl⟩
    rw [Set.uIcc_of_le hA0] at hx
    have hx1 : x < 1 := hx.2.trans_lt hA1
    have hφpos : 0 < φ x := by
      dsimp [φ]
      exact inv_pos.mpr (sub_pos.mpr hx1)
    have hrpow_ne :
        Real.rpow (φ x) (2 - 1 / n) ≠ 0 :=
      (Real.rpow_pos_of_pos hφpos _).ne'
    exact (Real.continuous_cos.continuousAt.div
      (Real.continuousAt_rpow_const (φ x) (2 - 1 / n)
        (Or.inl hφpos.ne')) hrpow_ne).continuousWithinAt
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv'
      (a := (0 : ℝ)) (b := A)
      (f := φ) (f' := φ') (g := g) hφ hφ' hg
  have hleft :
      (∫ x in (0 : ℝ)..A, (g ∘ φ) x * φ' x) =
        ∫ x in (0 : ℝ)..A,
          Real.cos (1 / (1 - x)) /
            Real.rpow (1 - x) (1 / n) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hA0] at hx
    have hx1 : x < 1 := hx.2.trans_lt hA1
    have hy : 0 < 1 - x := sub_pos.mpr hx1
    have hy0 : 1 - x ≠ 0 := hy.ne'
    dsimp [g, φ, φ']
    simp only [one_div]
    rw [Real.inv_rpow hy.le]
    rw [Real.rpow_sub hy]
    simp only [Real.rpow_two]
    field_simp [(Real.rpow_pos_of_pos hy (1 / n)).ne']
  rw [← hleft]
  simpa [φ, g] using hsub

private lemma singular_converges_iff_model_raw (n : ℝ) :
    (∃ L : ℝ,
      Tendsto
        (fun A : ℝ =>
          ∫ x in (0 : ℝ)..A,
            Real.cos (1 / (1 - x)) /
              Real.rpow (1 - x) (1 / n))
        (𝓝[<] (1 : ℝ)) (𝓝 L)) ↔
      (∃ L : ℝ,
        Tendsto
          (fun A : ℝ =>
            ∫ t in (1 : ℝ)..A,
              Real.cos t / Real.rpow t (2 - 1 / n))
          atTop (𝓝 L)) := by
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L, ?_⟩
    have hcomp := hL.comp one_sub_reciprocal_tendsto
    apply hcomp.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    dsimp only [Function.comp_apply]
    have hT0 : 0 < T := zero_lt_one.trans_le hT
    have hA0 : 0 ≤ 1 - 1 / T := by
      have hinv : 1 / T ≤ 1 := (div_le_one hT0).mpr hT
      linarith
    have hA1 : 1 - 1 / T < 1 := by
      have hinv : 0 < 1 / T := one_div_pos.mpr hT0
      linarith
    rw [singular_integral_substitution n (1 - 1 / T) hA0 hA1]
    congr 2
    field_simp
    ring
  · rintro ⟨L, hL⟩
    refine ⟨L, ?_⟩
    have hcomp := hL.comp reciprocal_one_sub_tendsto
    apply hcomp.congr'
    have hnonneg : ∀ᶠ A : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ A := by
      have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝[<] (1 : ℝ) := by
        exact (mem_nhdsLT_iff_exists_Ioo_subset).2
          ⟨0, (by exact Set.mem_Iio.mpr zero_lt_one),
            Set.Ioo_subset_Ioi_self⟩
      filter_upwards [hmem] with A hA
      exact hA.le
    filter_upwards [hnonneg, self_mem_nhdsWithin] with A hA0 hA1
    dsimp only [Function.comp_apply]
    exact (singular_integral_substitution n A hA0 hA1).symm

private lemma original_eq_factored_raw (n x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.cos (1 / (1 - x)) /
        Real.rpow (1 - x ^ 2) (1 / n) =
      Real.cos (1 / (1 - x)) /
        (Real.rpow (1 - x) (1 / n) *
          Real.rpow (1 + x) (1 / n)) := by
  have hminus : 0 ≤ 1 - x := (sub_pos.mpr hx1).le
  have hplus : 0 ≤ 1 + x := by linarith
  have hfac : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
  have hrpow :
      Real.rpow ((1 - x) * (1 + x)) (1 / n) =
        Real.rpow (1 - x) (1 / n) *
          Real.rpow (1 + x) (1 / n) :=
    Real.mul_rpow hminus hplus
  rw [hfac, hrpow]

private lemma original_integral_substitution
    (n A : ℝ) (hA0 : 0 ≤ A) (hA1 : A < 1) :
    (∫ x in (0 : ℝ)..A,
        Real.cos (1 / (1 - x)) /
          Real.rpow (1 - x ^ 2) (1 / n)) =
      ∫ t in (1 : ℝ)..(1 / (1 - A)),
        (Real.cos t / Real.rpow t (2 - 1 / n)) /
          Real.rpow (2 - 1 / t) (1 / n) := by
  let φ : ℝ → ℝ := fun x => (1 - x)⁻¹
  let φ' : ℝ → ℝ := fun x => ((1 - x) ^ 2)⁻¹
  let g : ℝ → ℝ :=
    fun t =>
      (Real.cos t / Real.rpow t (2 - 1 / n)) /
        Real.rpow (2 - 1 / t) (1 / n)
  have hφ : ∀ x ∈ Set.uIcc (0 : ℝ) A,
      HasDerivAt φ (φ' x) x := by
    intro x hx
    rw [Set.uIcc_of_le hA0] at hx
    have hx1 : x < 1 := hx.2.trans_lt hA1
    have hden : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
    have hraw := ((hasDerivAt_const x (1 : ℝ)).sub
      (hasDerivAt_id x)).inv hden
    simpa [φ, φ', one_div] using hraw
  have hφ' : ContinuousOn φ' (Set.uIcc (0 : ℝ) A) := by
    intro x hx
    rw [Set.uIcc_of_le hA0] at hx
    have hx1 : x < 1 := hx.2.trans_lt hA1
    have hden : (1 - x) ^ 2 ≠ 0 := pow_ne_zero 2
      (ne_of_gt (sub_pos.mpr hx1))
    dsimp [φ']
    exact (((continuousAt_const.sub continuousAt_id).pow 2).inv₀
      hden).continuousWithinAt
  have hg : ContinuousOn g (φ '' Set.uIcc (0 : ℝ) A) := by
    rintro t ⟨x, hx, rfl⟩
    rw [Set.uIcc_of_le hA0] at hx
    have hx1 : x < 1 := hx.2.trans_lt hA1
    have hφpos : 0 < φ x := by
      dsimp [φ]
      exact inv_pos.mpr (sub_pos.mpr hx1)
    have hbase : 0 < 2 - 1 / φ x := by
      dsimp [φ]
      simp only [one_div, inv_inv]
      linarith [hx.1]
    have hrpow₁ :
        Real.rpow (φ x) (2 - 1 / n) ≠ 0 :=
      (Real.rpow_pos_of_pos hφpos _).ne'
    have hrpow₂ :
        Real.rpow (2 - 1 / φ x) (1 / n) ≠ 0 :=
      (Real.rpow_pos_of_pos hbase _).ne'
    have hc1 :
        ContinuousAt
          (fun t : ℝ => Real.rpow t (2 - 1 / n)) (φ x) :=
      Real.continuousAt_rpow_const (φ x) (2 - 1 / n)
        (Or.inl hφpos.ne')
    have hinner :
        ContinuousAt (fun t : ℝ => 2 - 1 / t) (φ x) := by
      exact continuousAt_const.sub
        (continuousAt_const.div continuousAt_id hφpos.ne')
    have hc2 :
        ContinuousAt
          (fun t : ℝ => Real.rpow (2 - 1 / t) (1 / n)) (φ x) :=
      hinner.rpow_const (Or.inl hbase.ne')
    exact ((Real.continuous_cos.continuousAt.div hc1 hrpow₁).div
      hc2 hrpow₂).continuousWithinAt
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv'
      (a := (0 : ℝ)) (b := A)
      (f := φ) (f' := φ') (g := g) hφ hφ' hg
  have hleft :
      (∫ x in (0 : ℝ)..A, (g ∘ φ) x * φ' x) =
        ∫ x in (0 : ℝ)..A,
          Real.cos (1 / (1 - x)) /
            Real.rpow (1 - x ^ 2) (1 / n) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hA0] at hx
    have hx1 : x < 1 := hx.2.trans_lt hA1
    have hy : 0 < 1 - x := sub_pos.mpr hx1
    have hz : 0 < 1 + x := by linarith [hx.1]
    dsimp only [Function.comp_apply]
    rw [original_eq_factored_raw n x hx.1 hx1]
    dsimp [g, φ, φ']
    simp only [one_div]
    rw [Real.inv_rpow hy.le]
    rw [Real.rpow_sub hy]
    simp only [Real.rpow_two]
    have hinner : 2 - ((1 - x)⁻¹)⁻¹ = 1 + x := by
      rw [inv_inv]
      ring
    rw [hinner]
    field_simp [(Real.rpow_pos_of_pos hy (1 / n)).ne',
      (Real.rpow_pos_of_pos hz (1 / n)).ne']
  rw [← hleft]
  simpa [φ, g, one_div] using hsub

private def weight (q t : ℝ) : ℝ :=
  Real.rpow (2 - t⁻¹) (-q)

private def amplitude (α q t : ℝ) : ℝ :=
  Real.rpow t (-α) * weight q t

private def amplitudeDeriv (α q t : ℝ) : ℝ :=
  (-α * Real.rpow t (-α - 1)) * weight q t +
    (-q * Real.rpow t (-α - 2)) *
      Real.rpow (2 - t⁻¹) (-q - 1)

private lemma rpow_between_one_two_le (p s : ℝ)
    (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    Real.rpow s p ≤ max 1 (Real.rpow 2 p) := by
  by_cases hp : 0 ≤ p
  · exact (Real.rpow_le_rpow (zero_le_one.trans hs1) hs2 hp).trans
      (le_max_right _ _)
  · have hp' : p ≤ 0 := (lt_of_not_ge hp).le
    exact (Real.rpow_le_one_of_one_le_of_nonpos hs1 hp').trans
      (le_max_left _ _)

private lemma transformed_base_bounds (t : ℝ) (ht : 1 ≤ t) :
    1 ≤ 2 - 1 / t ∧ 2 - 1 / t ≤ 2 := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hinv0 : 0 ≤ 1 / t := (one_div_pos.mpr ht0).le
  have hinv1 : 1 / t ≤ 1 := (div_le_one ht0).mpr ht
  constructor <;> linarith

private lemma hasDerivAt_amplitude (α q t : ℝ) (ht : 1 ≤ t) :
    HasDerivAt (amplitude α q) (amplitudeDeriv α q t) t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hs := transformed_base_bounds t ht
  have hs0 : 0 < 2 - 1 / t := zero_lt_one.trans_le hs.1
  have hu :
      HasDerivAt (fun x : ℝ => Real.rpow x (-α))
        (-α * Real.rpow t (-α - 1)) t := by
    convert Real.hasDerivAt_rpow_const (x := t) (p := -α)
      (Or.inl ht0.ne') using 1 <;> ring
  have hinner :
      HasDerivAt (fun x : ℝ => 2 - x⁻¹) ((t ^ 2)⁻¹) t := by
    have hinv := (hasDerivAt_id t).inv ht0.ne'
    have hraw := (hasDerivAt_const t (2 : ℝ)).sub hinv
    have hfun :
        ((fun _ : ℝ => (2 : ℝ)) - (id : ℝ → ℝ)⁻¹) =
          fun x : ℝ => 2 - x⁻¹ := by
      funext x
      rfl
    rw [hfun] at hraw
    convert hraw using 1
    simp only [id_eq, one_div]
    ring
  have hw :
      HasDerivAt (weight q)
        ((-q * Real.rpow (2 - t⁻¹) (-q - 1)) *
          ((t ^ 2)⁻¹)) t := by
    have hout :
        HasDerivAt (fun s : ℝ => Real.rpow s (-q))
          (-q * Real.rpow (2 - t⁻¹) (-q - 1))
          (2 - t⁻¹) := by
      convert Real.hasDerivAt_rpow_const
        (x := 2 - t⁻¹) (p := -q) (Or.inl (by simpa [one_div] using hs0.ne'))
        using 1 <;> ring
    simpa [weight, Function.comp_def] using hout.comp t hinner
  have hprod := hu.mul hw
  have hprod' :
      HasDerivAt (amplitude α q)
        ((-α * Real.rpow t (-α - 1)) * weight q t +
          Real.rpow t (-α) *
            ((-q * Real.rpow (2 - t⁻¹) (-q - 1)) *
              ((t ^ 2)⁻¹))) t := by
    simpa [amplitude] using hprod
  convert hprod' using 1
  dsimp [amplitudeDeriv, weight]
  have hpow :
      Real.rpow t (-α) * (t ^ 2)⁻¹ =
        Real.rpow t (-α - 2) := by
    have hneg2 :
        (t ^ 2)⁻¹ = Real.rpow t (-2) := by
      calc
        (t ^ 2)⁻¹ = (Real.rpow t (2 : ℝ))⁻¹ := by
          exact congrArg Inv.inv (Real.rpow_two t).symm
        _ = Real.rpow t (-(2 : ℝ)) :=
          (Real.rpow_neg ht0.le 2).symm
        _ = Real.rpow t (-2) := rfl
    calc
      Real.rpow t (-α) * (t ^ 2)⁻¹ =
          Real.rpow t (-α) * Real.rpow t (-2) := by rw [hneg2]
      _ = Real.rpow t (-α + -2) := (Real.rpow_add ht0 _ _).symm
      _ = Real.rpow t (-α - 2) := by ring_nf
  have hsecond :
      (-q * Real.rpow t (-α - 2)) *
          Real.rpow (2 - t⁻¹) (-q - 1) =
        Real.rpow t (-α) *
          ((-q * Real.rpow (2 - t⁻¹) (-q - 1)) *
            (t ^ 2)⁻¹) := by
    rw [← hpow]
    ring
  exact congrArg
    (fun z : ℝ =>
      (-α * Real.rpow t (-α - 1)) *
          Real.rpow (2 - t⁻¹) (-q) + z)
    hsecond

private lemma continuousOn_amplitudeDeriv (α q : ℝ) :
    ContinuousOn (amplitudeDeriv α q) (Set.Ici 1) := by
  intro t ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have ht1 : 1 ≤ t := ht
  have hs := transformed_base_bounds t ht1
  have hs0 : 0 < 2 - t⁻¹ := by
    simpa [one_div] using (zero_lt_one.trans_le hs.1)
  have hinner :
      ContinuousAt (fun x : ℝ => 2 - x⁻¹) t :=
    continuousAt_const.sub (continuousAt_id.inv₀ ht0.ne')
  have ht_rpow (p : ℝ) :
      ContinuousAt (fun x : ℝ => Real.rpow x p) t :=
    Real.continuousAt_rpow_const t p (Or.inl ht0.ne')
  have hs_rpow (p : ℝ) :
      ContinuousAt (fun x : ℝ => Real.rpow (2 - x⁻¹) p) t :=
    hinner.rpow_const (Or.inl hs0.ne')
  exact ((((continuousAt_const.mul (ht_rpow (-α - 1))).mul
      (hs_rpow (-q))).add
        ((continuousAt_const.mul (ht_rpow (-α - 2))).mul
          (hs_rpow (-q - 1)))).continuousWithinAt)

private lemma amplitudeDeriv_integrable (α q : ℝ) (hα : 0 < α) :
    MeasureTheory.IntegrableOn (amplitudeDeriv α q) (Set.Ioi 1) := by
  let C₀ : ℝ := max 1 (Real.rpow 2 (-q))
  let C₁ : ℝ := max 1 (Real.rpow 2 (-q - 1))
  let majorant : ℝ → ℝ :=
    fun t =>
      (|α| * C₀) * Real.rpow t (-α - 1) +
        (|q| * C₁) * Real.rpow t (-α - 2)
  have hbase₀ :
      MeasureTheory.IntegrableOn
        (fun t : ℝ => Real.rpow t (-α - 1)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hbase₁ :
      MeasureTheory.IntegrableOn
        (fun t : ℝ => Real.rpow t (-α - 2)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hmajorant :
      MeasureTheory.IntegrableOn majorant (Set.Ioi 1) := by
    exact (hbase₀.const_mul (|α| * C₀)).add
      (hbase₁.const_mul (|q| * C₁))
  refine hmajorant.mono' ?_ ?_
  · exact ((continuousOn_amplitudeDeriv α q).mono
      Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with t ht
    have ht1 : 1 ≤ t := ht.le
    have ht0 : 0 ≤ t := zero_le_one.trans ht1
    have hs := transformed_base_bounds t ht1
    have hs' :
        1 ≤ 2 - t⁻¹ ∧ 2 - t⁻¹ ≤ 2 := by
      simpa [one_div] using hs
    have hw₀ :
        Real.rpow (2 - t⁻¹) (-q) ≤ C₀ := by
      exact rpow_between_one_two_le (-q) (2 - t⁻¹) hs'.1 hs'.2
    have hw₁ :
        Real.rpow (2 - t⁻¹) (-q - 1) ≤ C₁ := by
      exact rpow_between_one_two_le (-q - 1) (2 - t⁻¹)
        hs'.1 hs'.2
    have hs0 : 0 ≤ 2 - t⁻¹ := zero_le_one.trans hs'.1
    have hC₀ : 0 ≤ C₀ := le_trans zero_le_one (le_max_left _ _)
    have hC₁ : 0 ≤ C₁ := le_trans zero_le_one (le_max_left _ _)
    have ht₀pow : 0 ≤ Real.rpow t (-α - 1) :=
      Real.rpow_nonneg ht0 _
    have ht₁pow : 0 ≤ Real.rpow t (-α - 2) :=
      Real.rpow_nonneg ht0 _
    have hs₀pow : 0 ≤ Real.rpow (2 - t⁻¹) (-q) :=
      Real.rpow_nonneg hs0 _
    have hs₁pow : 0 ≤ Real.rpow (2 - t⁻¹) (-q - 1) :=
      Real.rpow_nonneg hs0 _
    rw [Real.norm_eq_abs]
    dsimp [amplitudeDeriv, weight, majorant]
    calc
      |(-α * Real.rpow t (-α - 1)) *
            Real.rpow (2 - t⁻¹) (-q) +
          (-q * Real.rpow t (-α - 2)) *
            Real.rpow (2 - t⁻¹) (-q - 1)| ≤
          |(-α * Real.rpow t (-α - 1)) *
              Real.rpow (2 - t⁻¹) (-q)| +
            |(-q * Real.rpow t (-α - 2)) *
              Real.rpow (2 - t⁻¹) (-q - 1)| :=
        abs_add_le _ _
      _ = |α| * Real.rpow t (-α - 1) *
              Real.rpow (2 - t⁻¹) (-q) +
            |q| * Real.rpow t (-α - 2) *
              Real.rpow (2 - t⁻¹) (-q - 1) := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_neg, abs_neg,
          abs_of_nonneg ht₀pow, abs_of_nonneg ht₁pow,
          abs_of_nonneg hs₀pow, abs_of_nonneg hs₁pow]
      _ ≤ (|α| * C₀) * Real.rpow t (-α - 1) +
            (|q| * C₁) * Real.rpow t (-α - 2) := by
        apply add_le_add
        · calc
            |α| * Real.rpow t (-α - 1) *
                Real.rpow (2 - t⁻¹) (-q) ≤
                |α| * Real.rpow t (-α - 1) * C₀ := by
              gcongr
            _ = (|α| * C₀) * Real.rpow t (-α - 1) := by
              ring
        · calc
            |q| * Real.rpow t (-α - 2) *
                Real.rpow (2 - t⁻¹) (-q - 1) ≤
                |q| * Real.rpow t (-α - 2) * C₁ := by
              gcongr
            _ = (|q| * C₁) * Real.rpow t (-α - 2) := by
              ring

private lemma weight_tendsto (q : ℝ) :
    Tendsto (weight q) atTop
      (𝓝 (Real.rpow 2 (-q))) := by
  have hinv :
      Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hinner :
      Tendsto (fun t : ℝ => 2 - t⁻¹) atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).sub hinv
  exact (Real.continuousAt_rpow_const 2 (-q)
    (Or.inl (by norm_num))).tendsto.comp hinner

private lemma amplitude_tendsto_zero (α q : ℝ) (hα : 0 < α) :
    Tendsto (amplitude α q) atTop (𝓝 0) := by
  have ht := tendsto_rpow_neg_atTop hα
  simpa [amplitude] using ht.mul (weight_tendsto q)

private lemma amplitude_times_sin_tendsto_zero
    (α q : ℝ) (hα : 0 < α) :
    Tendsto (fun t : ℝ => amplitude α q t * Real.sin t)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hamp := amplitude_tendsto_zero α q hα
  rw [Metric.tendsto_nhds] at hamp
  filter_upwards [hamp ε hε] with t ht
  rw [Real.dist_eq, sub_zero, abs_mul]
  rw [Real.dist_eq, sub_zero] at ht
  calc
    |amplitude α q t| * |Real.sin t| ≤
        |amplitude α q t| * 1 := by
      gcongr
      exact Real.abs_sin_le_one t
    _ = |amplitude α q t| := mul_one _
    _ < ε := ht

private lemma amplitude_ibp_formula
    (α q B : ℝ) (hB : 1 ≤ B) :
    (∫ t in (1 : ℝ)..B, amplitude α q t * Real.cos t) =
      amplitude α q B * Real.sin B -
        amplitude α q 1 * Real.sin 1 -
        ∫ t in (1 : ℝ)..B,
          amplitudeDeriv α q t * Real.sin t := by
  have hu : ∀ t ∈ Set.uIcc (1 : ℝ) B,
      HasDerivAt (amplitude α q) (amplitudeDeriv α q t) t := by
    intro t ht
    rw [Set.uIcc_of_le hB] at ht
    exact hasDerivAt_amplitude α q t ht.1
  have hv : ∀ t ∈ Set.uIcc (1 : ℝ) B,
      HasDerivAt Real.sin (Real.cos t) t :=
    fun t ht => Real.hasDerivAt_sin t
  have hu' :
      IntervalIntegrable (amplitudeDeriv α q)
        MeasureTheory.volume 1 B := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_amplitudeDeriv α q).mono
    intro t ht
    rw [Set.uIcc_of_le hB] at ht
    exact ht.1
  have hv' :
      IntervalIntegrable Real.cos MeasureTheory.volume 1 B :=
    Real.continuous_cos.intervalIntegrable _ _
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hu hv hu' hv'

private lemma weighted_eq_amplitude_mul_cos
    (α q t : ℝ) (ht : 1 ≤ t) :
    (Real.cos t / Real.rpow t α) /
        Real.rpow (2 - 1 / t) q =
      amplitude α q t * Real.cos t := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hs := transformed_base_bounds t ht
  have hs0 : 0 ≤ 2 - 1 / t := zero_le_one.trans hs.1
  dsimp [amplitude, weight]
  rw [Real.rpow_neg ht0, Real.rpow_neg (by simpa [one_div] using hs0)]
  simp [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

private lemma positive_weighted_converges (α q : ℝ) (hα : 0 < α) :
    ∃ L : ℝ,
      Tendsto
        (fun A : ℝ =>
          ∫ t in (1 : ℝ)..A,
            (Real.cos t / Real.rpow t α) /
              Real.rpow (2 - 1 / t) q)
        atTop (𝓝 L) := by
  let R : ℝ :=
    ∫ t : ℝ in Set.Ioi 1,
      amplitudeDeriv α q t * Real.sin t
  refine ⟨0 - amplitude α q 1 * Real.sin 1 - R, ?_⟩
  have hb := amplitude_times_sin_tendsto_zero α q hα
  have hrem_integrable :
      MeasureTheory.IntegrableOn
        (fun t : ℝ => amplitudeDeriv α q t * Real.sin t)
        (Set.Ioi 1) := by
    refine (amplitudeDeriv_integrable α q hα).norm.mono' ?_ ?_
    · exact (((continuousOn_amplitudeDeriv α q).mono
          Set.Ioi_subset_Ici_self).mul
        Real.continuous_sin.continuousOn).aestronglyMeasurable
        measurableSet_Ioi
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
        with t ht
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |amplitudeDeriv α q t| * |Real.sin t| ≤
            |amplitudeDeriv α q t| * 1 := by
          gcongr
          exact Real.abs_sin_le_one t
        _ = |amplitudeDeriv α q t| := mul_one _
        _ = ‖amplitudeDeriv α q t‖ := (Real.norm_eq_abs _).symm
  have hr :
      Tendsto
        (fun A : ℝ =>
          ∫ t in (1 : ℝ)..A,
            amplitudeDeriv α q t * Real.sin t)
        atTop (𝓝 R) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi
      1 hrem_integrable tendsto_id
  have hlim :=
    (hb.sub_const (amplitude α q 1 * Real.sin 1)).sub hr
  have hampint :
      Tendsto
        (fun A : ℝ =>
          ∫ t in (1 : ℝ)..A,
            amplitude α q t * Real.cos t)
        atTop (𝓝 (0 - amplitude α q 1 * Real.sin 1 - R)) := by
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with A hA
    exact (amplitude_ibp_formula α q A hA).symm
  apply hampint.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with A hA
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hA] at ht
  exact (weighted_eq_amplitude_mul_cos α q t ht.1).symm

private lemma amplitudeDeriv_zero_two_integrable :
    MeasureTheory.IntegrableOn (amplitudeDeriv 0 2) (Set.Ioi 1) := by
  have hbase :
      MeasureTheory.IntegrableOn
        (fun t : ℝ => Real.rpow t (-2)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hmajorant :
      MeasureTheory.IntegrableOn
        (fun t : ℝ => 2 * Real.rpow t (-2)) (Set.Ioi 1) :=
    hbase.const_mul 2
  refine hmajorant.mono' ?_ ?_
  · exact ((continuousOn_amplitudeDeriv 0 2).mono
      Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with t ht
    have ht1 : 1 ≤ t := ht.le
    have ht0 : 0 ≤ t := zero_le_one.trans ht1
    have hs := transformed_base_bounds t ht1
    have hs' :
        1 ≤ 2 - t⁻¹ ∧ 2 - t⁻¹ ≤ 2 := by
      simpa [one_div] using hs
    have hs0 : 0 ≤ 2 - t⁻¹ := zero_le_one.trans hs'.1
    have hw :
        Real.rpow (2 - t⁻¹) (-3) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hs'.1 (by norm_num)
    have htPow : 0 ≤ Real.rpow t (-2) := Real.rpow_nonneg ht0 _
    have hsPow : 0 ≤ Real.rpow (2 - t⁻¹) (-3) :=
      Real.rpow_nonneg hs0 _
    rw [Real.norm_eq_abs]
    have hderiv :
        amplitudeDeriv 0 2 t =
          (-2 * Real.rpow t (-2)) *
            Real.rpow (2 - t⁻¹) (-3) := by
      unfold amplitudeDeriv weight
      ring
    rw [hderiv]
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg htPow,
      abs_of_nonneg hsPow,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith

private lemma zero_weighted_not_converges :
    ¬ ∃ L : ℝ,
      Tendsto
        (fun A : ℝ =>
          ∫ t in (1 : ℝ)..A,
            (Real.cos t / Real.rpow t 0) /
              Real.rpow (2 - 1 / t) 2)
        atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hP :
      Tendsto
        (fun A : ℝ =>
          ∫ t in (1 : ℝ)..A,
            amplitude 0 2 t * Real.cos t)
        atTop (𝓝 L) := by
    apply hL.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with A hA
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hA] at ht
    exact weighted_eq_amplitude_mul_cos 0 2 t ht.1
  let R : ℝ :=
    ∫ t : ℝ in Set.Ioi 1,
      amplitudeDeriv 0 2 t * Real.sin t
  have hrem_integrable :
      MeasureTheory.IntegrableOn
        (fun t : ℝ => amplitudeDeriv 0 2 t * Real.sin t)
        (Set.Ioi 1) := by
    refine amplitudeDeriv_zero_two_integrable.norm.mono' ?_ ?_
    · exact ((((continuousOn_amplitudeDeriv 0 2).mono
          Set.Ioi_subset_Ici_self).mul
        Real.continuous_sin.continuousOn)).aestronglyMeasurable
          measurableSet_Ioi
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
        with t ht
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |amplitudeDeriv 0 2 t| * |Real.sin t| ≤
            |amplitudeDeriv 0 2 t| * 1 := by
          gcongr
          exact Real.abs_sin_le_one t
        _ = |amplitudeDeriv 0 2 t| := mul_one _
        _ = ‖amplitudeDeriv 0 2 t‖ := (Real.norm_eq_abs _).symm
  have hr :
      Tendsto
        (fun A : ℝ =>
          ∫ t in (1 : ℝ)..A,
            amplitudeDeriv 0 2 t * Real.sin t)
        atTop (𝓝 R) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi
      1 hrem_integrable tendsto_id
  have hboundary :
      Tendsto
        (fun A : ℝ => amplitude 0 2 A * Real.sin A)
        atTop
        (𝓝 (L + amplitude 0 2 1 * Real.sin 1 + R)) := by
    have hsum :=
      (hP.add_const (amplitude 0 2 1 * Real.sin 1)).add hr
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with A hA
    have hibp := amplitude_ibp_formula 0 2 A hA
    linarith
  have hamp :
      Tendsto (amplitude 0 2) atTop (𝓝 (1 / 4 : ℝ)) := by
    have hw := weight_tendsto 2
    have hwa :
        Tendsto (amplitude 0 2) atTop
          (𝓝 (Real.rpow 2 (-2))) := by
      apply hw.congr'
      filter_upwards [] with t
      simp [amplitude]
    have hval : Real.rpow 2 (-2) = (1 / 4 : ℝ) := by
      calc
        Real.rpow 2 (-2) = (Real.rpow 2 (2 : ℝ))⁻¹ :=
          Real.rpow_neg (by norm_num) 2
        _ = (1 / 4 : ℝ) := by
          rw [show Real.rpow 2 (2 : ℝ) = (2 : ℝ) ^ 2 from
            Real.rpow_two 2]
          norm_num
    rw [hval] at hwa
    exact hwa
  have hquot :=
    hboundary.div hamp (by norm_num : (1 / 4 : ℝ) ≠ 0)
  have hsin :
      Tendsto Real.sin atTop
        (𝓝 ((L + amplitude 0 2 1 * Real.sin 1 + R) /
          (1 / 4 : ℝ))) := by
    apply hquot.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 ≤ t := zero_le_one.trans ht
    have hs := transformed_base_bounds t ht
    have hs0 : 0 ≤ 2 - t⁻¹ := by
      simpa [one_div] using (zero_le_one.trans hs.1)
    have haPos : 0 < amplitude 0 2 t := by
      dsimp [amplitude, weight]
      exact mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le ht) _)
        (Real.rpow_pos_of_pos
          (zero_lt_one.trans_le (by simpa [one_div] using hs.1)) _)
    change
      amplitude 0 2 t * Real.sin t / amplitude 0 2 t =
        Real.sin t
    field_simp [haPos.ne']
  exact not_tendsto_sin_atTop _ hsin

private lemma negative_weighted_block_ge
    (β : ℝ) (hβ : 0 < β) (m : ℕ) (hm : 1 ≤ m) :
    Real.rpow 2 (-(2 + β)) *
        (∫ t in 2 * (m : ℝ) * Real.pi..
          2 * (m : ℝ) * Real.pi + Real.pi / 4,
          Real.rpow t β * Real.cos t) ≤
      ∫ t in 2 * (m : ℝ) * Real.pi..
        2 * (m : ℝ) * Real.pi + Real.pi / 4,
        amplitude (-β) (2 + β) t * Real.cos t := by
  let a : ℝ := 2 * (m : ℝ) * Real.pi
  let b : ℝ := a + Real.pi / 4
  have ha0 : 0 < a := by
    dsimp [a]
    positivity
  have hab : a < b := by
    dsimp [b]
    linarith [Real.pi_pos]
  have ha1 : 1 ≤ a := by
    have hmcast : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hmpi : Real.pi ≤ (m : ℝ) * Real.pi := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hmcast Real.pi_pos.le
    dsimp [a]
    nlinarith [Real.two_le_pi]
  have hcont₁ :
      ContinuousOn
        (fun t : ℝ =>
          Real.rpow 2 (-(2 + β)) *
            (Real.rpow t β * Real.cos t))
        (Set.uIcc a b) := by
    have hrpow :
        ContinuousOn (fun t : ℝ => Real.rpow t β)
          (Set.uIcc a b) := by
      intro t ht
      rw [Set.uIcc_of_le hab.le] at ht
      exact (Real.continuousAt_rpow_const t β
        (Or.inl (ne_of_gt (ha0.trans_le ht.1)))).continuousWithinAt
    exact continuousOn_const.mul
      (hrpow.mul Real.continuous_cos.continuousOn)
  have hcont₂ :
      ContinuousOn
        (fun t : ℝ =>
          amplitude (-β) (2 + β) t * Real.cos t)
        (Set.uIcc a b) := by
    intro t ht
    rw [Set.uIcc_of_le hab.le] at ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    have hs := transformed_base_bounds t (ha1.trans ht.1)
    have hs0 : 0 < 2 - t⁻¹ := by
      simpa [one_div] using (zero_lt_one.trans_le hs.1)
    have hinner :
        ContinuousAt (fun x : ℝ => 2 - x⁻¹) t :=
      continuousAt_const.sub (continuousAt_id.inv₀ ht0.ne')
    have ha :
        ContinuousAt (amplitude (-β) (2 + β)) t := by
      have htcont :
          ContinuousAt (fun x : ℝ => Real.rpow x β) t :=
        Real.continuousAt_rpow_const t β (Or.inl ht0.ne')
      have hwcont :
          ContinuousAt
            (fun x : ℝ =>
              Real.rpow (2 - x⁻¹) (-(2 + β))) t :=
        hinner.rpow_const (Or.inl hs0.ne')
      have hamp_eq :
          amplitude (-β) (2 + β) =
            fun x : ℝ =>
              Real.rpow x β *
                Real.rpow (2 - x⁻¹) (-(2 + β)) := by
        funext x
        simp [amplitude, weight]
      rw [hamp_eq]
      exact htcont.mul hwcont
    exact (ha.mul Real.continuous_cos.continuousAt).continuousWithinAt
  have hpoint : ∀ t ∈ Set.Icc a b,
      Real.rpow 2 (-(2 + β)) *
          (Real.rpow t β * Real.cos t) ≤
        amplitude (-β) (2 + β) t * Real.cos t := by
    intro t ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    have ht1 : 1 ≤ t := ha1.trans ht.1
    have hs := transformed_base_bounds t ht1
    have hs' :
        1 ≤ 2 - t⁻¹ ∧ 2 - t⁻¹ ≤ 2 := by
      simpa [one_div] using hs
    have hq : 0 < 2 + β := by linarith
    have hw :
        Real.rpow 2 (-(2 + β)) ≤
          Real.rpow (2 - t⁻¹) (-(2 + β)) :=
      Real.rpow_le_rpow_of_nonpos
        (zero_lt_one.trans_le hs'.1) hs'.2 (by linarith)
    have hphase : Real.cos t = Real.cos (t - a) := by
      have heq :
          t = (t - a) + m * (2 * Real.pi) := by
        dsimp [a]
        ring
      calc
        Real.cos t =
            Real.cos ((t - a) + m * (2 * Real.pi)) :=
          congrArg Real.cos heq
        _ = Real.cos (t - a) := by
          rw [Real.cos_add_nat_mul_two_pi]
    have hcos : 0 ≤ Real.cos t := by
      rw [hphase]
      have hdelta : t - a ∈ Set.Icc (0 : ℝ) (Real.pi / 4) := by
        have hta : a ≤ t := ht.1
        have htb : t ≤ a + Real.pi / 4 := by
          simpa [b] using ht.2
        constructor <;> linarith
      apply Real.cos_nonneg_of_mem_Icc
      constructor <;> linarith [Real.pi_pos, hdelta.1, hdelta.2]
    dsimp [amplitude, weight]
    simp only [neg_neg]
    have htpow : 0 ≤ Real.rpow t β :=
      Real.rpow_nonneg ht0.le _
    calc
      Real.rpow 2 (-(2 + β)) *
          (Real.rpow t β * Real.cos t) ≤
          Real.rpow (2 - t⁻¹) (-(2 + β)) *
            (Real.rpow t β * Real.cos t) := by
        gcongr
      _ = Real.rpow t β *
          Real.rpow (2 - t⁻¹) (-(2 + β)) *
            Real.cos t := by ring
  have hint₁ :
      IntervalIntegrable
        (fun t : ℝ =>
          Real.rpow 2 (-(2 + β)) *
            (Real.rpow t β * Real.cos t))
        MeasureTheory.volume a b :=
    hcont₁.intervalIntegrable
  have hint₂ :
      IntervalIntegrable
        (fun t : ℝ =>
          amplitude (-β) (2 + β) t * Real.cos t)
        MeasureTheory.volume a b :=
    hcont₂.intervalIntegrable
  have hmono :=
    intervalIntegral.integral_mono_on hab.le hint₁ hint₂ hpoint
  dsimp [a, b] at hmono
  calc
    Real.rpow 2 (-(2 + β)) *
        (∫ t in 2 * (m : ℝ) * Real.pi..
          2 * (m : ℝ) * Real.pi + Real.pi / 4,
          Real.rpow t β * Real.cos t) =
        ∫ t in 2 * (m : ℝ) * Real.pi..
          2 * (m : ℝ) * Real.pi + Real.pi / 4,
          Real.rpow 2 (-(2 + β)) *
            (Real.rpow t β * Real.cos t) := by
      exact
        (intervalIntegral.integral_const_mul
          (μ := MeasureTheory.volume)
          (a := 2 * (m : ℝ) * Real.pi)
          (b := 2 * (m : ℝ) * Real.pi + Real.pi / 4)
          (Real.rpow 2 (-(2 + β)))
          (fun t : ℝ => Real.rpow t β * Real.cos t)).symm
    _ ≤
        ∫ t in 2 * (m : ℝ) * Real.pi..
          2 * (m : ℝ) * Real.pi + Real.pi / 4,
          amplitude (-β) (2 + β) t * Real.cos t := hmono

private lemma negative_weighted_blocks_tendsto
    (β : ℝ) (hβ : 0 < β) :
    Tendsto
      (fun m : ℕ =>
        ∫ t in 2 * (m : ℝ) * Real.pi..
          2 * (m : ℝ) * Real.pi + Real.pi / 4,
          amplitude (-β) (2 + β) t * Real.cos t)
      atTop atTop := by
  have hc : 0 < Real.rpow 2 (-(2 + β)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hlower :
      Tendsto
        (fun m : ℕ =>
          Real.rpow 2 (-(2 + β)) *
            (∫ t in 2 * (m : ℝ) * Real.pi..
              2 * (m : ℝ) * Real.pi + Real.pi / 4,
              Real.rpow t β * Real.cos t))
        atTop atTop :=
    (block_integral_tendsto β hβ).const_mul_atTop hc
  rw [tendsto_atTop] at hlower ⊢
  intro c
  filter_upwards [hlower c, eventually_ge_atTop (1 : ℕ)]
      with m hmLower hm
  exact hmLower.trans (negative_weighted_block_ge β hβ m hm)

private lemma negative_weighted_not_converges
    (β : ℝ) (hβ : 0 < β) :
    ¬ ∃ L : ℝ,
      Tendsto
        (fun A : ℝ =>
          ∫ t in (1 : ℝ)..A,
            (Real.cos t / Real.rpow t (-β)) /
              Real.rpow (2 - 1 / t) (2 + β))
        atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hF :
      Tendsto
        (fun A : ℝ =>
          ∫ t in (1 : ℝ)..A,
            amplitude (-β) (2 + β) t * Real.cos t)
        atTop (𝓝 L) := by
    apply hL.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with A hA
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hA] at ht
    exact weighted_eq_amplitude_mul_cos (-β) (2 + β) t ht.1
  let a : ℕ → ℝ := fun m => 2 * (m : ℝ) * Real.pi
  let b : ℕ → ℝ := fun m => a m + Real.pi / 4
  have ha : Tendsto a atTop atTop := by
    have hmul :
        Tendsto (fun m : ℕ => (2 * Real.pi) * (m : ℝ))
          atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop
        (mul_pos two_pos Real.pi_pos)
    exact hmul.congr (fun m => by
      dsimp [a]
      ring)
  have hb : Tendsto b atTop atTop :=
    tendsto_atTop_add_const_right atTop (Real.pi / 4) ha
  have hFa := hF.comp ha
  have hFb := hF.comp hb
  have hzero :
      Tendsto
        (fun m : ℕ =>
          ∫ t in a m..b m,
            amplitude (-β) (2 + β) t * Real.cos t)
        atTop (𝓝 0) := by
    have hdiff :
        Tendsto
          (fun m : ℕ =>
            (∫ t in (1 : ℝ)..b m,
              amplitude (-β) (2 + β) t * Real.cos t) -
            ∫ t in (1 : ℝ)..a m,
              amplitude (-β) (2 + β) t * Real.cos t)
          atTop (𝓝 0) := by
      simpa using hFb.sub hFa
    apply hdiff.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have ha1 : 1 ≤ a m := by
      dsimp [a]
      have hmcast : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hmpi : Real.pi ≤ (m : ℝ) * Real.pi :=
        by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hmcast Real.pi_pos.le
      nlinarith [Real.two_le_pi]
    have hcont :
        ContinuousOn
          (fun t : ℝ =>
            amplitude (-β) (2 + β) t * Real.cos t)
          (Set.Ici 1) := by
      intro t ht
      have ht0 : 0 < t := zero_lt_one.trans_le ht
      have hs := transformed_base_bounds t ht
      have hs0 : 0 < 2 - t⁻¹ := by
        simpa [one_div] using (zero_lt_one.trans_le hs.1)
      have hinner :
          ContinuousAt (fun x : ℝ => 2 - x⁻¹) t :=
        continuousAt_const.sub (continuousAt_id.inv₀ ht0.ne')
      have hamp :
          ContinuousAt (amplitude (-β) (2 + β)) t := by
        have htcont :
            ContinuousAt (fun x : ℝ => Real.rpow x β) t :=
          Real.continuousAt_rpow_const t β (Or.inl ht0.ne')
        have hwcont :
            ContinuousAt
            (fun x : ℝ =>
                Real.rpow (2 - x⁻¹) (-(2 + β))) t :=
          hinner.rpow_const (Or.inl hs0.ne')
        have hamp_eq :
            amplitude (-β) (2 + β) =
              fun x : ℝ =>
                Real.rpow x β *
                  Real.rpow (2 - x⁻¹) (-(2 + β)) := by
          funext x
          simp [amplitude, weight]
        rw [hamp_eq]
        exact htcont.mul hwcont
      exact (hamp.mul Real.continuous_cos.continuousAt).continuousWithinAt
    have hint₁ :
        IntervalIntegrable
          (fun t : ℝ =>
            amplitude (-β) (2 + β) t * Real.cos t)
          MeasureTheory.volume 1 (a m) := by
      exact (hcont.mono (by
        intro t ht
        rw [Set.uIcc_of_le ha1] at ht
        exact ht.1)).intervalIntegrable
    have hint₂ :
        IntervalIntegrable
          (fun t : ℝ =>
            amplitude (-β) (2 + β) t * Real.cos t)
          MeasureTheory.volume (a m) (b m) := by
      exact (hcont.mono (by
        intro t ht
        rw [Set.uIcc_of_le (by
          dsimp [b]
          linarith [Real.pi_pos])] at ht
        exact ha1.trans ht.1)).intervalIntegrable
    have hadd :=
      intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂
    rw [← hadd]
    ring
  have htop :
      Tendsto
        (fun m : ℕ =>
          ∫ t in a m..b m,
            amplitude (-β) (2 + β) t * Real.cos t)
        atTop atTop := by
    convert negative_weighted_blocks_tendsto β hβ using 1
  exact not_tendsto_nhds_of_tendsto_atTop htop 0 hzero

private lemma weighted_converges_iff_relation_raw (α : ℝ) :
    (∃ L : ℝ,
      Tendsto
        (fun A : ℝ =>
          ∫ t in (1 : ℝ)..A,
            (Real.cos t / Real.rpow t α) /
              Real.rpow (2 - 1 / t) (2 - α))
        atTop (𝓝 L)) ↔
      0 < α := by
  constructor
  · intro hconv
    by_contra hnot
    have hle : α ≤ 0 := le_of_not_gt hnot
    rcases hle.eq_or_lt with hzero | hneg
    · subst α
      exact zero_weighted_not_converges (by simpa using hconv)
    · have hβ : 0 < -α := neg_pos.mpr hneg
      have hbad := negative_weighted_not_converges (-α) hβ
      apply hbad
      simpa using hconv
  · intro hα
    exact positive_weighted_converges α (2 - α) hα

private lemma original_converges_iff_weighted_raw (n : ℝ) :
    (∃ L : ℝ,
      Tendsto
        (fun A : ℝ =>
          ∫ x in (0 : ℝ)..A,
            Real.cos (1 / (1 - x)) /
              Real.rpow (1 - x ^ 2) (1 / n))
        (𝓝[<] (1 : ℝ)) (𝓝 L)) ↔
      (∃ L : ℝ,
        Tendsto
          (fun A : ℝ =>
            ∫ t in (1 : ℝ)..A,
              (Real.cos t / Real.rpow t (2 - 1 / n)) /
                Real.rpow (2 - 1 / t) (1 / n))
          atTop (𝓝 L)) := by
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L, ?_⟩
    have hcomp := hL.comp one_sub_reciprocal_tendsto
    apply hcomp.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    dsimp only [Function.comp_apply]
    have hT0 : 0 < T := zero_lt_one.trans_le hT
    have hA0 : 0 ≤ 1 - 1 / T := by
      have hinv : 1 / T ≤ 1 := (div_le_one hT0).mpr hT
      linarith
    have hA1 : 1 - 1 / T < 1 := by
      have hinv : 0 < 1 / T := one_div_pos.mpr hT0
      linarith
    rw [original_integral_substitution n (1 - 1 / T) hA0 hA1]
    congr 2
    field_simp
    ring
  · rintro ⟨L, hL⟩
    refine ⟨L, ?_⟩
    have hcomp := hL.comp reciprocal_one_sub_tendsto
    apply hcomp.congr'
    have hnonneg :
        ∀ᶠ A : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ A := by
      have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝[<] (1 : ℝ) := by
        exact (mem_nhdsLT_iff_exists_Ioo_subset).2
          ⟨0, (by exact Set.mem_Iio.mpr zero_lt_one),
            Set.Ioo_subset_Ioi_self⟩
      filter_upwards [hmem] with A hA
      exact hA.le
    filter_upwards [hnonneg, self_mem_nhdsWithin] with A hA0 hA1
    dsimp only [Function.comp_apply]
    exact (original_integral_substitution n A hA0 hA1).symm

private lemma original_converges_iff_condition_raw (n : ℝ) :
    (∃ L : ℝ,
      Tendsto
        (fun A : ℝ =>
          ∫ x in (0 : ℝ)..A,
            Real.cos (1 / (1 - x)) /
              Real.rpow (1 - x ^ 2) (1 / n))
        (𝓝[<] (1 : ℝ)) (𝓝 L)) ↔
      0 < 2 - 1 / n := by
  rw [original_converges_iff_weighted_raw]
  have h :=
    weighted_converges_iff_relation_raw (2 - 1 / n)
  have hexp : 2 - (2 - 1 / n) = 1 / n := by ring
  rw [hexp] at h
  exact h

private lemma singular_converges_iff_condition_raw (n : ℝ) :
    (∃ L : ℝ,
      Tendsto
        (fun A : ℝ =>
          ∫ x in (0 : ℝ)..A,
            Real.cos (1 / (1 - x)) /
              Real.rpow (1 - x) (1 / n))
        (𝓝[<] (1 : ℝ)) (𝓝 L)) ↔
      0 < 2 - 1 / n :=
  (singular_converges_iff_model_raw n).trans
    (model_converges_iff_raw (2 - 1 / n))

namespace ProofGap.Exercise3745

noncomputable section

open Filter
open scoped Interval Topology

def originalIntegrand (n x : ℝ) : ℝ :=
  Real.cos (1 / (1 - x)) / Real.rpow (1 - x ^ 2) (1 / n)

def factoredIntegrand (n x : ℝ) : ℝ :=
  Real.cos (1 / (1 - x)) /
    (Real.rpow (1 - x) (1 / n) * Real.rpow (1 + x) (1 / n))

def partialIntegral (n A : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..A, originalIntegrand n x

def Converges (n : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (partialIntegral n) (𝓝[<] (1 : ℝ)) (𝓝 L)

def singularPartialIntegral (n A : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..A,
    Real.cos (1 / (1 - x)) / Real.rpow (1 - x) (1 / n)

def SingularConverges (n : ℝ) : Prop :=
  ∃ L : ℝ,
    Tendsto (singularPartialIntegral n) (𝓝[<] (1 : ℝ)) (𝓝 L)

def modelPartialIntegral (α A : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..A, Real.cos t / Real.rpow t α

def ModelConverges (α : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (modelPartialIntegral α) atTop (𝓝 L)

theorem gap1 (n x : ℝ) (hn : n ≠ 0)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    originalIntegrand n x = factoredIntegrand n x := by
  unfold originalIntegrand factoredIntegrand
  exact original_eq_factored_raw n x hx.1 hx.2

theorem gap2 (n : ℝ) (hn : n ≠ 0) :
    Converges n ↔ SingularConverges n := by
  unfold Converges partialIntegral SingularConverges singularPartialIntegral
  exact (original_converges_iff_condition_raw n).trans
    (singular_converges_iff_condition_raw n).symm

theorem gap3 (n : ℝ) (hn : n ≠ 0) :
    SingularConverges n ↔ ModelConverges (2 - 1 / n) := by
  unfold SingularConverges singularPartialIntegral
    ModelConverges modelPartialIntegral
  exact singular_converges_iff_model_raw n

theorem gap4 (α : ℝ) :
    ModelConverges α ↔ 0 < α := by
  unfold ModelConverges modelPartialIntegral
  exact model_converges_iff_raw α

theorem gap5 :
    ¬ ModelConverges 0 := by
  unfold ModelConverges modelPartialIntegral
  exact zero_model_not_converges

theorem gap6 (α : ℝ) (hα : α < 0) :
    0 < -α := by
  exact neg_pos.mpr hα

theorem gap7 (β : ℝ) (hβ : 0 < β) (m : ℕ) (hm : 1 ≤ m) :
    (∫ t in 2 * (m : ℝ) * Real.pi..
          2 * (m : ℝ) * Real.pi + Real.pi / 4,
          Real.rpow t β * Real.cos t) >
      Real.rpow (2 * (m : ℝ) * Real.pi) β *
        (1 / Real.sqrt 2) * (Real.pi / 4) := by
  exact block_lower β hβ m hm

theorem gap8 (β : ℝ) (hβ : 0 < β) :
    Tendsto
      (fun m : ℕ =>
        Real.rpow (2 * (m : ℝ) * Real.pi) β *
          (1 / Real.sqrt 2) * (Real.pi / 4))
      atTop atTop := by
  exact block_lower_tendsto β hβ

theorem gap9 (β : ℝ) (hβ : 0 < β) :
    Tendsto
      (fun m : ℕ =>
        ∫ t in 2 * (m : ℝ) * Real.pi..
          2 * (m : ℝ) * Real.pi + Real.pi / 4,
          Real.rpow t β * Real.cos t)
      atTop atTop := by
  exact block_integral_tendsto β hβ

theorem gap10 (α : ℝ) (hα : α < 0) :
    ¬ ModelConverges α := by
  unfold ModelConverges modelPartialIntegral
  have hβ : 0 < -α := neg_pos.mpr hα
  have hbad := negative_model_not_converges (-α) hβ
  simpa using hbad

theorem gap11 (n : ℝ) (hn : n ≠ 0) :
    Converges n ↔ 0 < 2 - 1 / n := by
  unfold Converges partialIntegral
  exact original_converges_iff_condition_raw n

theorem gap12 (n : ℝ) (hn : n ≠ 0) :
    (n < 0 ∨ 1 / 2 < n) ↔ Converges n := by
  rw [gap11 n hn]
  constructor
  · rintro (hneg | hlarge)
    · have hinv : 1 / n < 0 := one_div_neg.mpr hneg
      linarith
    · have hnpos : 0 < n := by linarith
      have hmul : 1 < 2 * n := by linarith
      have hinv : 1 / n < 2 := (div_lt_iff₀ hnpos).2 hmul
      linarith
  · intro hcondition
    by_cases hneg : n < 0
    · exact Or.inl hneg
    · right
      have hnpos : 0 < n := lt_of_le_of_ne
        (le_of_not_gt hneg) (Ne.symm hn)
      have hinv : 1 / n < 2 := by linarith
      have hmul : 1 < 2 * n := (div_lt_iff₀ hnpos).1 hinv
      linarith

end

end ProofGap.Exercise3745
