import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3817

noncomputable section

open Filter MeasureTheory
open scoped Interval

def sincSquare (α x : ℝ) : ℝ :=
  (Real.sin (α * x) / x) ^ 2

def I (α : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), sincSquare α x

def HasDirichletValue (γ L : ℝ) : Prop :=
  Tendsto (fun A : ℝ => ∫ x in (0 : ℝ)..A, Real.sin (γ * x) / x)
    atTop (nhds L)

def dirichletValue (γ : ℝ) : ℝ :=
  sInf {L : ℝ | HasDirichletValue γ L}

def parameterDerivativeValue (α : ℝ) : ℝ :=
  sInf {L : ℝ |
    Tendsto
      (fun A : ℝ => ∫ x in (0 : ℝ)..A,
        deriv (fun a : ℝ => sincSquare a x) α)
      atTop (nhds L)}

-- Statement correction: the quotient used in `sincSquare` is assigned the value zero at
-- `x = 0`, so its continuous-extension limit is necessarily a punctured-neighborhood limit.
theorem gap1 (α : ℝ) (hα : 0 ≤ α) :
    Tendsto (fun x : ℝ => sincSquare α x)
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds (α ^ 2)) := by
  have hcont :
      Tendsto (fun x : ℝ => (α * Real.sinc (α * x)) ^ 2) (nhds 0) (nhds (α ^ 2)) := by
    have hc : Continuous (fun x : ℝ => (α * Real.sinc (α * x)) ^ 2) :=
      ((Real.continuous_sinc.comp (continuous_const.mul continuous_id)).const_mul α).pow 2
    have hca : ContinuousAt (fun x : ℝ => (α * Real.sinc (α * x)) ^ 2) 0 :=
      hc.continuousAt
    change Tendsto (fun x : ℝ => (α * Real.sinc (α * x)) ^ 2) (nhds 0)
      (nhds ((α * Real.sinc (α * 0)) ^ 2)) at hca
    simpa only [mul_zero, Real.sinc_zero, mul_one] using hca
  apply (hcont.mono_left inf_le_left).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  rcases eq_or_ne α 0 with rfl | hα0
  · simp [sincSquare]
  · rw [Real.sinc_of_ne_zero (mul_ne_zero hα0 hx0)]
    unfold sincSquare
    field_simp
    <;> ring

theorem gap2 (α x : ℝ) (hα : 0 ≤ α) (hx : x ≠ 0) :
    sincSquare α x ≤ 1 / x ^ 2 := by
  unfold sincSquare
  rw [div_pow]
  exact div_le_div_of_nonneg_right (Real.sin_sq_le_one (α * x)) (sq_nonneg x)

private theorem I_eq_mul_I_one_of_pos (α : ℝ) (hα : 0 < α) :
    I α = α * I 1 := by
  have hchange :=
    integral_comp_mul_left_Ioi (sincSquare 1) 0 hα
  simp only [mul_zero, smul_eq_mul] at hchange
  unfold I
  calc
    (∫ x in Set.Ioi (0 : ℝ), sincSquare α x) =
        ∫ x in Set.Ioi (0 : ℝ), α ^ 2 * sincSquare 1 (α * x) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          have hx0 : x ≠ 0 := ne_of_gt hx
          have hax0 : α * x ≠ 0 := mul_ne_zero hα.ne' hx0
          unfold sincSquare
          field_simp
          <;> ring
    _ = α ^ 2 * ∫ x in Set.Ioi (0 : ℝ), sincSquare 1 (α * x) := by
          rw [MeasureTheory.integral_const_mul]
    _ = α ^ 2 * (α⁻¹ * ∫ x in Set.Ioi (0 : ℝ), sincSquare 1 x) := by
          rw [hchange]
    _ = α * ∫ x in Set.Ioi (0 : ℝ), sincSquare 1 x := by
          field_simp
    _ = α * I 1 := rfl

private theorem I_eq_mul_I_one_of_nonneg (α : ℝ) (hα : 0 ≤ α) :
    I α = α * I 1 := by
  rcases hα.eq_or_lt with rfl | hpos
  · simp [I, sincSquare]
  · exact I_eq_mul_I_one_of_pos α hpos

theorem gap3 :
    ContinuousOn I (Set.Ici (0 : ℝ)) := by
  have hc : Continuous (fun α : ℝ => α * I 1) :=
    continuous_id.mul continuous_const
  apply hc.continuousOn.congr
  intro α hα
  exact I_eq_mul_I_one_of_nonneg α hα

private theorem hasDerivAt_sincSquare_parameter (α x : ℝ) :
    HasDerivAt (fun a : ℝ => sincSquare a x)
      (Real.sin ((2 * α) * x) / x) α := by
  rcases eq_or_ne x 0 with rfl | hx
  · simpa [sincSquare] using (hasDerivAt_const α (0 : ℝ))
  · have hinner : HasDerivAt (fun a : ℝ => a * x) x α := by
      simpa using (hasDerivAt_id α).mul_const x
    have hquot :
        HasDerivAt (fun a : ℝ => Real.sin (a * x) / x)
          (Real.cos (α * x)) α := by
      convert ((Real.hasDerivAt_sin (α * x)).comp α hinner).div_const x using 1
      field_simp
    convert hquot.pow 2 using 1
    rw [show 2 * α * x = 2 * (α * x) by ring]
    rw [Real.sin_two_mul]
    simp only [Nat.cast_ofNat, Nat.reduceSubDiff, pow_one]
    field_simp [hx]
    <;> ring

private theorem deriv_sincSquare_parameter (α x : ℝ) :
    deriv (fun a : ℝ => sincSquare a x) α =
      Real.sin ((2 * α) * x) / x :=
  (hasDerivAt_sincSquare_parameter α x).deriv

private theorem integral_exp_mul_cos_Ioi (s γ : ℝ) (hs : 0 < s) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-s * x) * Real.cos (γ * x)) =
      s / (s ^ 2 + γ ^ 2) := by
  let z : ℂ := (-s : ℂ) + (γ : ℂ) * Complex.I
  have hz : z.re < 0 := by
    simp [z]
    linarith
  have hint : IntegrableOn (fun x : ℝ => Complex.exp (z * (x : ℂ))) (Set.Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hz 0
  have hpoint (x : ℝ) :
      (Complex.exp (z * (x : ℂ))).re =
        Real.exp (-s * x) * Real.cos (γ * x) := by
    rw [Complex.exp_re]
    simp [z]
  calc
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-s * x) * Real.cos (γ * x)) =
        ∫ x in Set.Ioi (0 : ℝ), (Complex.exp (z * (x : ℂ))).re := by
          apply integral_congr_ae
          filter_upwards with x
          exact (hpoint x).symm
    _ = (∫ x in Set.Ioi (0 : ℝ), Complex.exp (z * (x : ℂ))).re :=
      integral_re hint
    _ = (-Complex.exp (z * (0 : ℂ)) / z).re := by
      simpa using congrArg Complex.re (integral_exp_mul_complex_Ioi hz 0)
    _ = s / (s ^ 2 + γ ^ 2) := by
      simp [z, Complex.div_re, Complex.normSq_apply]
      ring

private def dampedDirichlet (s γ : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), Real.exp (-s * x) * (Real.sin (γ * x) / x)

private theorem integrableOn_dampedDirichlet (s γ : ℝ) (hs : 0 < s) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-s * x) * (Real.sin (γ * x) / x))
      (Set.Ioi 0) := by
  have hexp : IntegrableOn (fun x : ℝ => Real.exp (-s * x)) (Set.Ioi 0) := by
    convert integrableOn_exp_mul_Ioi (a := -s) (by linarith) 0 using 1
  have hbound :
      Integrable (fun x : ℝ => |γ| * Real.exp (-s * x))
        (volume.restrict (Set.Ioi 0)) :=
    hexp.const_mul |γ|
  apply hbound.mono'
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_div,
      abs_of_pos hx0]
    have hsin := Real.abs_sin_le_abs (x := γ * x)
    rw [abs_mul, abs_of_pos hx0] at hsin
    calc
      Real.exp (-s * x) * (|Real.sin (γ * x)| / x) ≤
          Real.exp (-s * x) * ((|γ| * x) / x) := by gcongr
      _ = |γ| * Real.exp (-s * x) := by
        field_simp

private theorem dampedDirichlet_hasDerivAt (s γ : ℝ) (hs : 0 < s) :
    HasDerivAt (dampedDirichlet s)
      (s / (s ^ 2 + γ ^ 2)) γ := by
  let F : ℝ → ℝ → ℝ :=
    fun a x => Real.exp (-s * x) * (Real.sin (a * x) / x)
  let F' : ℝ → ℝ → ℝ :=
    fun a x => Real.exp (-s * x) * Real.cos (a * x)
  have hbound :
      Integrable (fun x : ℝ => Real.exp (-s * x))
        (volume.restrict (Set.Ioi 0)) := by
    exact integrableOn_exp_mul_Ioi (a := -s) (by linarith) 0
  have hres :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioi 0))
      (F := F) (F' := F') (bound := fun x : ℝ => Real.exp (-s * x))
      (s := Set.univ) (x₀ := γ)
      univ_mem
      (by
        filter_upwards with a
        exact (integrableOn_dampedDirichlet s a hs).aestronglyMeasurable)
      (integrableOn_dampedDirichlet s γ hs)
      (by fun_prop)
      (by
        filter_upwards with x a ha
        dsimp [F']
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_of_le_one_right (Real.exp_nonneg _) (Real.abs_cos_le_one _))
      hbound
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx a ha
        have hx0 : x ≠ 0 := ne_of_gt hx
        dsimp [F, F']
        convert
          (hasDerivAt_const a (Real.exp (-s * x))).mul
            (((Real.hasDerivAt_sin (a * x)).comp a
              ((hasDerivAt_id a).mul_const x)).div_const x) using 1
        field_simp [hx0]
        <;> ring)
  unfold dampedDirichlet
  convert hres.2 using 1
  exact (integral_exp_mul_cos_Ioi s γ hs).symm

private theorem dampedDirichlet_eq_arctan (s γ : ℝ) (hs : 0 < s) :
    dampedDirichlet s γ = Real.arctan (γ / s) := by
  let H : ℝ → ℝ := fun a => dampedDirichlet s a - Real.arctan (a / s)
  have harctan (a : ℝ) :
      HasDerivAt (fun y : ℝ => Real.arctan (y / s))
        (s / (s ^ 2 + a ^ 2)) a := by
    convert (Real.hasDerivAt_arctan (a / s)).comp a
      ((hasDerivAt_id a).div_const s) using 1
    field_simp [hs.ne']
    <;> ring
  have hH (a : ℝ) : HasDerivAt H 0 a := by
    dsimp [H]
    convert (dampedDirichlet_hasDerivAt s a hs).sub (harctan a) using 1
    ring
  have hconst := is_const_of_deriv_eq_zero
    (f := H) (fun a => (hH a).differentiableAt)
    (fun a => by rw [(hH a).deriv]) γ 0
  have hzero : H 0 = 0 := by
    simp [H, dampedDirichlet]
  rw [hzero] at hconst
  exact sub_eq_zero.mp hconst

private theorem integral_inv_sq (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x : ℝ in a..b, (x ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
  have hz : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    simp only [Set.mem_Icc, not_and_or]
    exact Or.inl (not_le.mpr ha)
  have h := integral_zpow (a := a) (b := b) (n := (-2 : ℤ))
    (Or.inr ⟨by norm_num, hz⟩)
  norm_num [zpow_neg, div_eq_mul_inv] at h ⊢
  exact h

private theorem dirichlet_tail_identity
    (γ a b : ℝ) (hγ : 0 < γ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x : ℝ in a..b, Real.sin (γ * x) / x) =
      -Real.cos (γ * b) / (γ * b) + Real.cos (γ * a) / (γ * a) -
        ∫ x : ℝ in a..b, Real.cos (γ * x) / (γ * x ^ 2) := by
  have hxpos {x : ℝ} (hx : x ∈ Set.uIcc a b) : 0 < x := by
    rw [Set.uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hu : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := by
    intro x hx
    exact hasDerivAt_inv (ne_of_gt (hxpos hx))
  have hv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => -Real.cos (γ * y) / γ) (Real.sin (γ * x)) x := by
    intro x hx
    convert
      (((Real.hasDerivAt_cos (γ * x)).comp x
        ((hasDerivAt_const x γ).mul (hasDerivAt_id x))).neg.div_const γ) using 1
    field_simp [hγ.ne']
    <;> ring
  have hu' : IntervalIntegrable (fun y : ℝ => -(y ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact ((continuousAt_id.pow 2).inv₀
      (pow_ne_zero 2 (ne_of_gt (hxpos hx)))).neg.continuousWithinAt
  have hv' : IntervalIntegrable (fun y : ℝ => Real.sin (γ * y)) volume a b :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable a b
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  convert hibp using 1 <;> field_simp [hγ.ne'] <;> ring

private theorem norm_dirichlet_tail_le
    (γ a b : ℝ) (hγ : 0 < γ) (ha : 0 < a) (hab : a ≤ b) :
    |∫ x : ℝ in a..b, Real.sin (γ * x) / x| ≤ 3 / (γ * a) := by
  have hb : 0 < b := ha.trans_le hab
  have hpow := integral_inv_sq a b ha hab
  have hgint : IntervalIntegrable (fun x : ℝ => (1 / γ) * (x ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := ne_of_gt (ha.trans_le hx.1)
    exact (continuousAt_const.mul
      ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 hx0))).continuousWithinAt
  have hrem :
      |∫ x : ℝ in a..b, Real.cos (γ * x) / (γ * x ^ 2)| ≤
        (1 / γ) * (a⁻¹ - b⁻¹) := by
    calc
      |∫ x : ℝ in a..b, Real.cos (γ * x) / (γ * x ^ 2)| =
          ‖∫ x : ℝ in a..b, Real.cos (γ * x) / (γ * x ^ 2)‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ∫ x : ℝ in a..b, (1 / γ) * (x ^ 2)⁻¹ := by
        apply intervalIntegral.norm_integral_le_of_norm_le hab
        · filter_upwards with x hx
          have hxpos : 0 < x := ha.trans hx.1
          rw [Real.norm_eq_abs, div_eq_mul_inv, abs_mul, abs_inv, abs_mul,
            abs_of_pos hγ, abs_of_pos (sq_pos_of_pos hxpos), one_div, mul_inv_rev]
          calc
            |Real.cos (γ * x)| * ((x ^ 2)⁻¹ * γ⁻¹) ≤
                1 * ((x ^ 2)⁻¹ * γ⁻¹) := by
                  gcongr
                  exact Real.abs_cos_le_one _
            _ = γ⁻¹ * (x ^ 2)⁻¹ := by ring
        · exact hgint
      _ = (1 / γ) * (a⁻¹ - b⁻¹) := by
        rw [intervalIntegral.integral_const_mul, hpow]
  have hba : 1 / b ≤ 1 / a := one_div_le_one_div_of_le ha hab
  have hterm_b :
      |-Real.cos (γ * b) / (γ * b)| ≤ 1 / (γ * b) := by
    rw [abs_div, abs_neg, abs_mul, abs_of_pos hγ, abs_of_pos hb]
    gcongr
    exact Real.abs_cos_le_one _
  have hterm_a :
      |Real.cos (γ * a) / (γ * a)| ≤ 1 / (γ * a) := by
    rw [abs_div, abs_mul, abs_of_pos hγ, abs_of_pos ha]
    gcongr
    exact Real.abs_cos_le_one _
  rw [dirichlet_tail_identity γ a b hγ ha hab]
  calc
    |-Real.cos (γ * b) / (γ * b) + Real.cos (γ * a) / (γ * a) -
        ∫ x : ℝ in a..b, Real.cos (γ * x) / (γ * x ^ 2)| ≤
      |-Real.cos (γ * b) / (γ * b)| + |Real.cos (γ * a) / (γ * a)| +
        |∫ x : ℝ in a..b, Real.cos (γ * x) / (γ * x ^ 2)| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_add_le _ _
    _ ≤ 1 / (γ * b) + 1 / (γ * a) + (1 / γ) * (a⁻¹ - b⁻¹) := by
      gcongr
    _ ≤ 3 / (γ * a) := by
      have hγ0 : 0 ≤ 1 / γ := le_of_lt (one_div_pos.mpr hγ)
      have hinv : b⁻¹ ≤ a⁻¹ := by simpa only [one_div] using hba
      field_simp [hγ.ne', ha.ne', hb.ne']
      nlinarith

private theorem intervalIntegrable_dirichlet (γ A : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.sin (γ * x) / x) volume 0 A := by
  have hp :
      IntervalIntegrable (fun x : ℝ => γ * Real.sinc (γ * x)) volume 0 A := by
    have hc : Continuous (fun x : ℝ => γ * Real.sinc (γ * x)) :=
      (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).const_mul γ
    exact hc.intervalIntegrable 0 A
  apply hp.congr_ae
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_of_ae hne] with x hx
  rcases eq_or_ne γ 0 with rfl | hγ
  · simp
  · rw [Real.sinc_of_ne_zero (mul_ne_zero hγ hx)]
    field_simp

private theorem exists_dirichlet_limit (γ : ℝ) (hγ : 0 < γ) :
    ∃ L : ℝ, Tendsto
      (fun A : ℝ => ∫ x in (0 : ℝ)..A, Real.sin (γ * x) / x)
      atTop (nhds L) := by
  let F : ℝ → ℝ := fun A => ∫ x in (0 : ℝ)..A, Real.sin (γ * x) / x
  suffices Cauchy (Filter.map F atTop) by
    exact cauchy_map_iff_exists_tendsto.mp this
  rw [Metric.cauchy_iff]
  constructor
  · exact (inferInstance : NeBot (atTop : Filter ℝ)).map F
  · intro ε hε
    let N : ℝ := 6 / (γ * ε)
    have hN : 0 < N := div_pos (by norm_num) (mul_pos hγ hε)
    refine ⟨F '' Set.Ici N, ?_, ?_⟩
    · change F ⁻¹' (F '' Set.Ici N) ∈ atTop
      filter_upwards [eventually_ge_atTop N] with A hA
      exact ⟨A, hA, rfl⟩
    · intro u hu v hv
      rcases hu with ⟨A, hA, rfl⟩
      rcases hv with ⟨B, hB, rfl⟩
      have hApos : 0 < A := hN.trans_le hA
      have hBpos : 0 < B := hN.trans_le hB
      have hsmallA : 3 / (γ * A) < ε := by
        have h6 : 6 ≤ A * (γ * ε) := (div_le_iff₀ (mul_pos hγ hε)).mp hA
        rw [div_lt_iff₀ (mul_pos hγ hApos)]
        nlinarith
      have hsmallB : 3 / (γ * B) < ε := by
        have h6 : 6 ≤ B * (γ * ε) := (div_le_iff₀ (mul_pos hγ hε)).mp hB
        rw [div_lt_iff₀ (mul_pos hγ hBpos)]
        nlinarith
      rcases le_total A B with hAB | hBA
      · have hdiff :
            F B - F A = ∫ x in A..B, Real.sin (γ * x) / x := by
          exact intervalIntegral.integral_interval_sub_left
            (intervalIntegrable_dirichlet γ B) (intervalIntegrable_dirichlet γ A)
        rw [Real.dist_eq, abs_sub_comm, hdiff]
        exact (norm_dirichlet_tail_le γ A B hγ hApos hAB).trans_lt hsmallA
      · have hdiff :
            F A - F B = ∫ x in B..A, Real.sin (γ * x) / x := by
          exact intervalIntegral.integral_interval_sub_left
            (intervalIntegrable_dirichlet γ A) (intervalIntegrable_dirichlet γ B)
        rw [Real.dist_eq, hdiff]
        exact (norm_dirichlet_tail_le γ B A hγ hBpos hBA).trans_lt hsmallB

private theorem damped_tail_identity
    (s γ a b : ℝ) (hs : 0 < s) (hγ : 0 < γ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x : ℝ in a..b, Real.exp (-s * x) * (Real.sin (γ * x) / x)) =
      -Real.exp (-s * b) * Real.cos (γ * b) / (γ * b) +
        Real.exp (-s * a) * Real.cos (γ * a) / (γ * a) -
        ∫ x : ℝ in a..b,
          Real.exp (-s * x) * (s / x + 1 / x ^ 2) * Real.cos (γ * x) / γ := by
  have hxpos {x : ℝ} (hx : x ∈ Set.uIcc a b) : 0 < x := by
    rw [Set.uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hu : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => Real.exp (-s * y) / y)
        (-Real.exp (-s * x) * (s / x + 1 / x ^ 2)) x := by
    intro x hx
    have hx0 := ne_of_gt (hxpos hx)
    have he :
        HasDerivAt (fun y : ℝ => Real.exp (-s * y))
          (-s * Real.exp (-s * x)) x := by
      convert Real.hasDerivAt_exp (-s * x) |>.comp x
        ((hasDerivAt_const x (-s)).mul (hasDerivAt_id x)) using 1
      ring
    convert he.div (hasDerivAt_id x) hx0 using 1
    simp only [id_eq]
    field_simp [hx0]
    <;> ring
  have hv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => -Real.cos (γ * y) / γ) (Real.sin (γ * x)) x := by
    intro x hx
    convert
      (((Real.hasDerivAt_cos (γ * x)).comp x
        ((hasDerivAt_const x γ).mul (hasDerivAt_id x))).neg.div_const γ) using 1
    field_simp [hγ.ne']
    <;> ring
  have hu' :
      IntervalIntegrable
        (fun x : ℝ => -Real.exp (-s * x) * (s / x + 1 / x ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx0 := ne_of_gt (hxpos hx)
    have hec : ContinuousAt (fun y : ℝ => Real.exp (-s * y)) x :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt
    have hdiv1 : ContinuousAt (fun y : ℝ => s / y) x :=
      continuousAt_const.div continuousAt_id hx0
    have hdiv2 : ContinuousAt (fun y : ℝ => 1 / y ^ 2) x :=
      continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hx0)
    exact (hec.neg.mul (hdiv1.add hdiv2)).continuousWithinAt
  have hv' : IntervalIntegrable (fun y : ℝ => Real.sin (γ * y)) volume a b :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable a b
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hrem :
      (∫ x : ℝ in a..b,
        -Real.exp (-s * x) * (s / x + 1 / x ^ 2) * (-Real.cos (γ * x) / γ)) =
      ∫ x : ℝ in a..b,
        Real.exp (-s * x) * (s / x + 1 / x ^ 2) * Real.cos (γ * x) / γ := by
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  calc
    (∫ x : ℝ in a..b, Real.exp (-s * x) * (Real.sin (γ * x) / x)) =
        ∫ x : ℝ in a..b, (Real.exp (-s * x) / x) * Real.sin (γ * x) := by
          apply intervalIntegral.integral_congr
          intro x hx
          ring
    _ = Real.exp (-s * b) / b * (-Real.cos (γ * b) / γ) -
        Real.exp (-s * a) / a * (-Real.cos (γ * a) / γ) -
        ∫ x : ℝ in a..b,
          -Real.exp (-s * x) * (s / x + 1 / x ^ 2) * (-Real.cos (γ * x) / γ) :=
      hibp
    _ = _ := by
      rw [hrem]
      field_simp [hγ.ne', ha.ne', (ha.trans_le hab).ne']
      <;> ring

private theorem integral_damped_weight
    (s a b : ℝ) (hs : 0 < s) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x : ℝ in a..b, Real.exp (-s * x) * (s / x + 1 / x ^ 2)) =
      Real.exp (-s * a) / a - Real.exp (-s * b) / b := by
  have hxpos {x : ℝ} (hx : x ∈ Set.uIcc a b) : 0 < x := by
    rw [Set.uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => -Real.exp (-s * y) / y)
        (Real.exp (-s * x) * (s / x + 1 / x ^ 2)) x := by
    intro x hx
    have hx0 := ne_of_gt (hxpos hx)
    have he :
        HasDerivAt (fun y : ℝ => Real.exp (-s * y))
          (-s * Real.exp (-s * x)) x := by
      convert Real.hasDerivAt_exp (-s * x) |>.comp x
        ((hasDerivAt_const x (-s)).mul (hasDerivAt_id x)) using 1
      ring
    convert (he.div (hasDerivAt_id x) hx0).neg using 1
    · funext y
      simp [div_eq_mul_inv]
    · simp only [id_eq]
      field_simp [hx0]
      <;> ring
  have hint :
      IntervalIntegrable
        (fun x : ℝ => Real.exp (-s * x) * (s / x + 1 / x ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx0 := ne_of_gt (hxpos hx)
    have hec : ContinuousAt (fun y : ℝ => Real.exp (-s * y)) x :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt
    have hdiv1 : ContinuousAt (fun y : ℝ => s / y) x :=
      continuousAt_const.div continuousAt_id hx0
    have hdiv2 : ContinuousAt (fun y : ℝ => 1 / y ^ 2) x :=
      continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hx0)
    exact (hec.mul (hdiv1.add hdiv2)).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  convert h using 1 <;> ring

private theorem norm_damped_tail_le
    (s γ a b : ℝ) (hs : 0 < s) (hγ : 0 < γ) (ha : 0 < a) (hab : a ≤ b) :
    |∫ x : ℝ in a..b, Real.exp (-s * x) * (Real.sin (γ * x) / x)| ≤
      2 / (γ * a) := by
  have hb : 0 < b := ha.trans_le hab
  have hweight := integral_damped_weight s a b hs ha hab
  have hgint :
      IntervalIntegrable
        (fun x : ℝ => (1 / γ) * (Real.exp (-s * x) * (s / x + 1 / x ^ 2)))
        volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := ne_of_gt (ha.trans_le hx.1)
    have hec : ContinuousAt (fun y : ℝ => Real.exp (-s * y)) x :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt
    have hdiv1 : ContinuousAt (fun y : ℝ => s / y) x :=
      continuousAt_const.div continuousAt_id hx0
    have hdiv2 : ContinuousAt (fun y : ℝ => 1 / y ^ 2) x :=
      continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hx0)
    exact (continuousAt_const.mul (hec.mul (hdiv1.add hdiv2))).continuousWithinAt
  have hrem :
      |∫ x : ℝ in a..b,
          Real.exp (-s * x) * (s / x + 1 / x ^ 2) * Real.cos (γ * x) / γ| ≤
        (1 / γ) * (Real.exp (-s * a) / a - Real.exp (-s * b) / b) := by
    calc
      |∫ x : ℝ in a..b,
          Real.exp (-s * x) * (s / x + 1 / x ^ 2) * Real.cos (γ * x) / γ| =
        ‖∫ x : ℝ in a..b,
          Real.exp (-s * x) * (s / x + 1 / x ^ 2) * Real.cos (γ * x) / γ‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ∫ x : ℝ in a..b,
          (1 / γ) * (Real.exp (-s * x) * (s / x + 1 / x ^ 2)) := by
        apply intervalIntegral.norm_integral_le_of_norm_le hab
        · filter_upwards with x hx
          have hxpos : 0 < x := ha.trans hx.1
          have hsum : 0 ≤ s / x + 1 / x ^ 2 := by positivity
          rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
            abs_of_pos (Real.exp_pos _), abs_of_nonneg hsum, abs_of_pos hγ]
          calc
            Real.exp (-s * x) * (s / x + 1 / x ^ 2) * |Real.cos (γ * x)| / γ ≤
              Real.exp (-s * x) * (s / x + 1 / x ^ 2) * 1 / γ := by
                gcongr
                exact Real.abs_cos_le_one _
            _ = (1 / γ) * (Real.exp (-s * x) * (s / x + 1 / x ^ 2)) := by ring
        · exact hgint
      _ = (1 / γ) * (Real.exp (-s * a) / a - Real.exp (-s * b) / b) := by
        rw [intervalIntegral.integral_const_mul, hweight]
  have hterm_b :
      |-Real.exp (-s * b) * Real.cos (γ * b) / (γ * b)| ≤
        Real.exp (-s * b) / (γ * b) := by
    rw [abs_div, abs_mul, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos hγ, abs_of_pos hb]
    apply (div_le_div_iff_of_pos_right (mul_pos hγ hb)).2
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (γ * b)) (Real.exp_nonneg (-s * b))
  have hterm_a :
      |Real.exp (-s * a) * Real.cos (γ * a) / (γ * a)| ≤
        Real.exp (-s * a) / (γ * a) := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos hγ, abs_of_pos ha]
    apply (div_le_div_iff_of_pos_right (mul_pos hγ ha)).2
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (γ * a)) (Real.exp_nonneg (-s * a))
  have hexp_le : Real.exp (-s * a) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) ha.le)
  rw [damped_tail_identity s γ a b hs hγ ha hab]
  calc
    |-Real.exp (-s * b) * Real.cos (γ * b) / (γ * b) +
        Real.exp (-s * a) * Real.cos (γ * a) / (γ * a) -
        ∫ x : ℝ in a..b,
          Real.exp (-s * x) * (s / x + 1 / x ^ 2) * Real.cos (γ * x) / γ| ≤
      |-Real.exp (-s * b) * Real.cos (γ * b) / (γ * b)| +
        |Real.exp (-s * a) * Real.cos (γ * a) / (γ * a)| +
        |∫ x : ℝ in a..b,
          Real.exp (-s * x) * (s / x + 1 / x ^ 2) * Real.cos (γ * x) / γ| := by
            refine (abs_sub _ _).trans ?_
            gcongr
            exact abs_add_le _ _
    _ ≤ Real.exp (-s * b) / (γ * b) + Real.exp (-s * a) / (γ * a) +
        (1 / γ) * (Real.exp (-s * a) / a - Real.exp (-s * b) / b) := by
      gcongr
    _ ≤ 2 / (γ * a) := by
      rw [show
        Real.exp (-s * b) / (γ * b) + Real.exp (-s * a) / (γ * a) +
            (1 / γ) * (Real.exp (-s * a) / a - Real.exp (-s * b) / b) =
          2 * Real.exp (-s * a) / (γ * a) by
            field_simp [hγ.ne', ha.ne', hb.ne']
            <;> ring]
      apply (div_le_div_iff_of_pos_right (mul_pos hγ ha)).2
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hexp_le (show (0 : ℝ) ≤ 2 by norm_num)

private theorem norm_damped_Ioi_tail_le
    (s γ A : ℝ) (hs : 0 < s) (hγ : 0 < γ) (hA : 0 < A) :
    |dampedDirichlet s γ -
        ∫ x in (0 : ℝ)..A, Real.exp (-s * x) * (Real.sin (γ * x) / x)| ≤
      2 / (γ * A) := by
  let f : ℝ → ℝ :=
    fun x => Real.exp (-s * x) * (Real.sin (γ * x) / x)
  have hint0 : IntegrableOn f (Set.Ioi 0) :=
    integrableOn_dampedDirichlet s γ hs
  have hintA : IntegrableOn f (Set.Ioi A) :=
    hint0.mono_set (Set.Ioi_subset_Ioi hA.le)
  have hlim :
      Tendsto (fun b : ℝ => ∫ x in A..b, f x) atTop
        (nhds (∫ x in Set.Ioi A, f x)) :=
    intervalIntegral_tendsto_integral_Ioi A hintA tendsto_id
  have htail_set :
      |∫ x in Set.Ioi A, f x| ≤ 2 / (γ * A) := by
    apply le_of_tendsto hlim.abs
    filter_upwards [eventually_ge_atTop A] with b hb
    exact norm_damped_tail_le s γ A b hs hγ hA hb
  have hIoc : IntegrableOn f (Set.Ioc 0 A) :=
    hint0.mono_set (by
      intro x hx
      exact hx.1)
  have hsplit :
      dampedDirichlet s γ =
        (∫ x in (0 : ℝ)..A, f x) + ∫ x in Set.Ioi A, f x := by
    unfold dampedDirichlet
    rw [show Set.Ioi (0 : ℝ) = Set.Ioc 0 A ∪ Set.Ioi A by
      ext x
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro hx
        by_cases h : x ≤ A
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr (lt_of_not_ge h)
      · rintro (hx | hx)
        · exact hx.1
        · exact hA.trans hx]
    rw [setIntegral_union]
    · rw [intervalIntegral.integral_of_le hA.le]
    · exact Set.disjoint_left.2 (by
        intro x hxIoc hxIoi
        exact (not_lt_of_ge hxIoc.2) hxIoi)
    · exact measurableSet_Ioi
    · exact hIoc
    · exact hintA
  rw [hsplit]
  simpa [f] using htail_set

private theorem norm_damped_cutoff_sub_le
    (s γ A : ℝ) (hs : 0 < s) (hA : 0 < A) :
    |(∫ x in (0 : ℝ)..A, Real.exp (-s * x) * (Real.sin (γ * x) / x)) -
        ∫ x in (0 : ℝ)..A, Real.sin (γ * x) / x| ≤ s * A := by
  let fd : ℝ → ℝ :=
    fun x => Real.exp (-s * x) * (Real.sin (γ * x) / x)
  let f : ℝ → ℝ := fun x => Real.sin (γ * x) / x
  have hfd : IntervalIntegrable fd volume 0 A := by
    rw [intervalIntegrable_iff]
    exact (integrableOn_dampedDirichlet s γ hs).mono_set (by
      intro x hx
      rw [Set.uIoc_of_le hA.le] at hx
      exact hx.1)
  have hf : IntervalIntegrable f volume 0 A :=
    intervalIntegrable_dirichlet γ A
  rw [← intervalIntegral.integral_sub hfd hf]
  calc
    |∫ x in (0 : ℝ)..A, fd x - f x| =
        ‖∫ x in (0 : ℝ)..A, fd x - f x‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ x in (0 : ℝ)..A, s := by
      apply intervalIntegral.norm_integral_le_of_norm_le hA.le
      · filter_upwards with x hx
        have hxpos : 0 < x := hx.1
        have he_le : Real.exp (-s * x) ≤ 1 :=
          Real.exp_le_one_iff.mpr
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) hxpos.le)
        have he :
            |Real.exp (-s * x) - 1| ≤ s * x := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr he_le)]
          nlinarith [Real.add_one_le_exp (-s * x)]
        have hsin :
            |Real.sin (γ * x) / x| ≤ 1 / x := by
          rw [abs_div, abs_of_pos hxpos]
          gcongr
          exact Real.abs_sin_le_one _
        dsimp [fd, f]
        rw [show
          Real.exp (-s * x) * (Real.sin (γ * x) / x) - Real.sin (γ * x) / x =
            (Real.exp (-s * x) - 1) * (Real.sin (γ * x) / x) by ring]
        calc
          ‖(Real.exp (-s * x) - 1) * (Real.sin (γ * x) / x)‖ =
              |Real.exp (-s * x) - 1| * |Real.sin (γ * x) / x| := by
                rw [Real.norm_eq_abs, abs_mul]
          _ ≤ (s * x) * (1 / x) := by
            gcongr
          _ = s := by
            field_simp
      · exact (continuous_const : Continuous fun _ : ℝ => s).intervalIntegrable 0 A
    _ = s * A := by
      simp [intervalIntegral.integral_const]
      ring

private theorem dirichlet_tendsto_pi_div_two (γ : ℝ) (hγ : 0 < γ) :
    Tendsto
      (fun A : ℝ => ∫ x in (0 : ℝ)..A, Real.sin (γ * x) / x)
      atTop (nhds (Real.pi / 2)) := by
  rcases exists_dirichlet_limit γ hγ with ⟨L, hL⟩
  let A : ℕ → ℝ := fun n => (n : ℝ) + 1
  let s : ℕ → ℝ := fun n => 1 / (A n) ^ 2
  let D : ℕ → ℝ := fun n => dampedDirichlet (s n) γ
  let F : ℕ → ℝ :=
    fun n => ∫ x in (0 : ℝ)..A n, Real.sin (γ * x) / x
  have hApos (n : ℕ) : 0 < A n := by
    dsimp [A]
    positivity
  have hspos (n : ℕ) : 0 < s n := by
    dsimp [s]
    positivity
  have hdiff_bound (n : ℕ) :
      ‖D n - F n‖ ≤ (2 / γ + 1) * (1 / A n) := by
    let C : ℝ :=
      ∫ x in (0 : ℝ)..A n, Real.exp (-s n * x) * (Real.sin (γ * x) / x)
    have htail := norm_damped_Ioi_tail_le (s n) γ (A n)
      (hspos n) hγ (hApos n)
    have hcut := norm_damped_cutoff_sub_le (s n) γ (A n)
      (hspos n) (hApos n)
    dsimp [D, F] at htail ⊢
    change |dampedDirichlet (s n) γ -
      (∫ x in (0 : ℝ)..A n, Real.sin (γ * x) / x)| ≤ _
    calc
      |dampedDirichlet (s n) γ -
          (∫ x in (0 : ℝ)..A n, Real.sin (γ * x) / x)| ≤
        |dampedDirichlet (s n) γ - C| +
          |C - ∫ x in (0 : ℝ)..A n, Real.sin (γ * x) / x| := by
            rw [show dampedDirichlet (s n) γ -
                (∫ x in (0 : ℝ)..A n, Real.sin (γ * x) / x) =
              (dampedDirichlet (s n) γ - C) +
                (C - ∫ x in (0 : ℝ)..A n, Real.sin (γ * x) / x) by ring]
            exact abs_add_le _ _
      _ ≤ 2 / (γ * A n) + s n * A n := by
        exact add_le_add htail hcut
      _ = (2 / γ + 1) * (1 / A n) := by
        dsimp [s]
        field_simp [(hApos n).ne']
        <;> ring
  have hinv :
      Tendsto (fun n : ℕ => 1 / A n) atTop (nhds 0) := by
    simpa [A] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0))
  have hboundlim :
      Tendsto (fun n : ℕ => (2 / γ + 1) * (1 / A n)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hinv)
  have hdiff : Tendsto (fun n => D n - F n) atTop (nhds 0) :=
    squeeze_zero_norm hdiff_bound hboundlim
  have hAtop : Tendsto A atTop atTop := by
    dsimp [A]
    exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hF : Tendsto F atTop (nhds L) := by
    exact hL.comp hAtop
  have hDtoL : Tendsto D atTop (nhds L) := by
    simpa only [zero_add, sub_add_cancel] using hdiff.add hF
  have hAsq : Tendsto (fun n => A n * A n) atTop atTop :=
    hAtop.atTop_mul_atTop₀ hAtop
  have harg :
      Tendsto (fun n => γ * (A n * A n)) atTop atTop :=
    Tendsto.const_mul_atTop hγ hAsq
  have hatan :
      Tendsto (fun n => Real.arctan (γ * (A n * A n))) atTop
        (nhds (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right inf_le_left).comp harg
  have hDpi : Tendsto D atTop (nhds (Real.pi / 2)) := by
    apply hatan.congr'
    filter_upwards with n
    dsimp [D]
    rw [dampedDirichlet_eq_arctan (s n) γ (hspos n)]
    congr 1
    dsimp [s]
    field_simp [(hApos n).ne']
    <;> ring
  have hLeq : L = Real.pi / 2 :=
    tendsto_nhds_unique hDtoL hDpi
  simpa [hLeq] using hL

theorem gap4 (α : ℝ) :
    parameterDerivativeValue α = dirichletValue (2 * α) := by
  unfold parameterDerivativeValue dirichletValue
  congr 1
  ext L
  simp only [deriv_sincSquare_parameter, HasDirichletValue]

theorem gap5 (α : ℝ) (hα : 0 < α) :
    dirichletValue (2 * α) = Real.pi / 2 := by
  have hγ : 0 < 2 * α := mul_pos (by norm_num) hα
  have hlim := dirichlet_tendsto_pi_div_two (2 * α) hγ
  have hset :
      {L : ℝ | HasDirichletValue (2 * α) L} = {Real.pi / 2} := by
    ext L
    constructor
    · intro hL
      have heq : L = Real.pi / 2 :=
        tendsto_nhds_unique hL hlim
      simpa [heq]
    · intro hL
      have heq : L = Real.pi / 2 := by simpa using hL
      simpa [HasDirichletValue, heq] using hlim
  unfold dirichletValue
  rw [hset]
  simp

theorem gap6 (α : ℝ) (hα : 0 < α) :
    parameterDerivativeValue α = Real.pi / 2 := by
  exact (gap4 α).trans (gap5 α hα)

private theorem intervalIntegrable_sincSquare (α A : ℝ) :
    IntervalIntegrable (sincSquare α) volume 0 A := by
  have hp :
      IntervalIntegrable
        (fun x : ℝ => (α * Real.sinc (α * x)) ^ 2) volume 0 A := by
    have hc : Continuous (fun x : ℝ => (α * Real.sinc (α * x)) ^ 2) :=
      ((Real.continuous_sinc.comp (continuous_const.mul continuous_id)).const_mul α).pow 2
    exact hc.intervalIntegrable 0 A
  apply hp.congr_ae
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_of_ae hne] with x hx
  rcases eq_or_ne α 0 with rfl | hα
  · simp [sincSquare]
  · rw [Real.sinc_of_ne_zero (mul_ne_zero hα hx)]
    unfold sincSquare
    field_simp
    <;> ring

private theorem sincSquare_cutoff_identity (A : ℝ) (hA : 0 < A) :
    (∫ x in (0 : ℝ)..A, sincSquare 1 x) =
      (∫ x in (0 : ℝ)..A, Real.sin (2 * x) / x) -
        Real.sin A ^ 2 / A := by
  let g : ℝ → ℝ := fun x => Real.sin x ^ 2 / x
  have hg_eq : g = fun x : ℝ => x * Real.sinc x ^ 2 := by
    funext x
    rcases eq_or_ne x 0 with rfl | hx
    · simp [g]
    · rw [Real.sinc_of_ne_zero hx]
      dsimp [g]
      field_simp
      <;> ring
  have hgcont : ContinuousOn g (Set.Icc 0 A) := by
    rw [hg_eq]
    exact (continuous_id.mul (Real.continuous_sinc.pow 2)).continuousOn
  have hgderiv : ∀ x ∈ Set.Ioo 0 A,
      HasDerivAt g (Real.sin (2 * x) / x - sincSquare 1 x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    dsimp [g]
    convert ((Real.hasDerivAt_sin x).pow 2).div (hasDerivAt_id x) hx0 using 1
    simp only [id_eq, Pi.pow_apply]
    rw [Real.sin_two_mul]
    unfold sincSquare
    field_simp [hx0]
    <;> ring
  have hdir : IntervalIntegrable (fun x : ℝ => Real.sin (2 * x) / x) volume 0 A :=
    intervalIntegrable_dirichlet 2 A
  have hsq : IntervalIntegrable (sincSquare 1) volume 0 A :=
    intervalIntegrable_sincSquare 1 A
  have hsub := hdir.sub hsq
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hA.le hgcont hgderiv hsub
  rw [intervalIntegral.integral_sub hdir hsq] at hftc
  dsimp [g] at hftc
  simp only [Real.sin_zero, zero_pow, zero_div, sub_zero] at hftc
  linarith

private theorem boundary_sin_sq_div_tendsto_zero :
    Tendsto (fun A : ℝ => Real.sin A ^ 2 / A) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun A : ℝ => A⁻¹)
    (Eventually.of_forall fun A => norm_nonneg (Real.sin A ^ 2 / A)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with A hA
    have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos hApos]
    simpa only [one_div] using
      (div_le_div_of_nonneg_right (Real.sin_sq_le_one A) hApos.le)
  · exact (tendsto_inv_atTop_zero :
      Tendsto (fun A : ℝ => A⁻¹) atTop (nhds 0))

private theorem sincSquare_one_tendsto_pi_div_two :
    Tendsto (fun A : ℝ => ∫ x in (0 : ℝ)..A, sincSquare 1 x)
      atTop (nhds (Real.pi / 2)) := by
  have hdir := dirichlet_tendsto_pi_div_two 2 (by norm_num)
  have hsub := hdir.sub boundary_sin_sq_div_tendsto_zero
  have hsub' :
      Tendsto
        (fun A : ℝ =>
          (∫ x in (0 : ℝ)..A, Real.sin (2 * x) / x) -
            Real.sin A ^ 2 / A)
        atTop (nhds (Real.pi / 2)) := by
    simpa using hsub
  apply hsub'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
  exact (sincSquare_cutoff_identity A hA).symm

private theorem integrableOn_sincSquare_one :
    IntegrableOn (sincSquare 1) (Set.Ioi 0) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  have hcover : AECover μ atTop (fun A : ℝ => Set.Iic A) :=
    aecover_Iic tendsto_id
  apply hcover.integrable_of_integral_bounded_of_nonneg_ae (Real.pi / 2 + 1)
  · intro A
    by_cases hA : 0 < A
    · have hi := intervalIntegrable_sincSquare 1 A
      rw [intervalIntegrable_iff, Set.uIoc_of_le hA.le] at hi
      have hset : Set.Iic A ∩ Set.Ioi (0 : ℝ) = Set.Ioc 0 A := by
        ext x
        simp [and_comm]
      simpa [μ, IntegrableOn, Measure.restrict_restrict measurableSet_Iic, hset] using hi
    · have hempty : Set.Iic A ∩ Set.Ioi (0 : ℝ) = ∅ := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi, Set.mem_empty_iff_false,
          iff_false]
        exact fun hx => (not_lt_of_ge (hx.1.trans (le_of_not_gt hA))) hx.2
      simp [μ, IntegrableOn, Measure.restrict_restrict measurableSet_Iic, hempty]
  · filter_upwards with x
    exact sq_nonneg _
  · have hev :
        ∀ᶠ A : ℝ in atTop,
          (∫ x in (0 : ℝ)..A, sincSquare 1 x) ≤ Real.pi / 2 + 1 := by
      have hnhds :
          Set.Iio (Real.pi / 2 + 1) ∈ nhds (Real.pi / 2) := by
        exact Iio_mem_nhds (by linarith)
      filter_upwards [sincSquare_one_tendsto_pi_div_two.eventually hnhds] with A hA
      exact hA.le
    filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with A hbound hA
    rw [Measure.restrict_restrict measurableSet_Iic]
    have hset : Set.Iic A ∩ Set.Ioi (0 : ℝ) = Set.Ioc 0 A := by
      ext x
      simp [and_comm]
    rw [hset]
    rw [← intervalIntegral.integral_of_le hA]
    exact hbound

private theorem I_one_eq_pi_div_two :
    I 1 = Real.pi / 2 := by
  have hproper :=
    intervalIntegral_tendsto_integral_Ioi 0 integrableOn_sincSquare_one tendsto_id
  exact tendsto_nhds_unique hproper sincSquare_one_tendsto_pi_div_two

theorem gap7 (α : ℝ) (hα : 0 < α) :
    deriv I α = Real.pi / 2 := by
  have heq : I =ᶠ[nhds α] fun a : ℝ => a * I 1 := by
    filter_upwards [Ioi_mem_nhds hα] with a ha
    exact I_eq_mul_I_one_of_pos a ha
  have hderiv : HasDerivAt (fun a : ℝ => a * I 1) (I 1) α := by
    simpa using (hasDerivAt_id α).mul_const (I 1)
  have hI : HasDerivAt I (I 1) α :=
    hderiv.congr_of_eventuallyEq heq
  rw [hI.deriv, I_one_eq_pi_div_two]

theorem gap8 :
    ∃ C : ℝ, ∀ α : ℝ, 0 < α →
      I α = Real.pi / 2 * α + C := by
  refine ⟨0, ?_⟩
  intro α hα
  rw [I_eq_mul_I_one_of_pos α hα, I_one_eq_pi_div_two]
  ring

theorem gap9 :
    I 0 = 0 := by
  unfold I sincSquare
  simp

theorem gap10 :
    ∃ C : ℝ,
      (∀ α : ℝ, 0 < α → I α = Real.pi / 2 * α + C) ∧
      I 0 = C := by
  refine ⟨0, ?_, gap9⟩
  intro α hα
  rw [I_eq_mul_I_one_of_pos α hα, I_one_eq_pi_div_two]
  ring

theorem gap11 :
    ∃ C : ℝ,
      (∀ α : ℝ, 0 < α → I α = Real.pi / 2 * α + C) ∧
      C = 0 := by
  rcases gap10 with ⟨C, hC, h0⟩
  exact ⟨C, hC, (by simpa [gap9] using h0 : (0 : ℝ) = C).symm⟩

theorem gap12 (α : ℝ) (hα : 0 ≤ α) :
    I α = Real.pi / 2 * α := by
  rcases gap11 with ⟨C, hC, hC0⟩
  subst C
  rcases hα.eq_or_lt with rfl | hpos
  · simpa using gap9
  · simpa using hC α hpos

theorem gap13 (α : ℝ) (hα : α < 0) :
    I α = I (-α) := by
  unfold I sincSquare
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [neg_mul, Real.sin_neg]
  ring

theorem gap14 (α : ℝ) (hα : α < 0) :
    I (-α) = Real.pi / 2 * (-α) := by
  exact gap12 (-α) (neg_nonneg.mpr hα.le)

theorem gap15 (α : ℝ) (hα : α < 0) :
    I α = Real.pi / 2 * (-α) := by
  exact (gap13 α hα).trans (gap14 α hα)

theorem gap16 (α : ℝ) :
    I α = Real.pi / 2 * |α| := by
  rcases le_total 0 α with hα | hα
  · rw [abs_of_nonneg hα]
    exact gap12 α hα
  · rcases hα.eq_or_lt with hzero | hneg
    · subst α
      simp [gap9]
    · rw [abs_of_neg hneg]
      exact gap15 α hneg

end

end ProofGap.Exercise3817
