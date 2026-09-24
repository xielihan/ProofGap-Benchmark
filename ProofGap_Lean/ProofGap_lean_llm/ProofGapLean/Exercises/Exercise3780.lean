import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3780

noncomputable section

open Filter MeasureTheory Set
open scoped Interval Topology

def integrand (α x : ℝ) : ℝ :=
  Real.cos x / Real.rpow x α

def HasOscillatoryIntegral (α L : ℝ) : Prop :=
  Tendsto (fun A : ℝ => ∫ x in (1 : ℝ)..A, integrand α x)
    atTop (nhds L)

def F (α : ℝ) : ℝ :=
  sInf {L : ℝ | HasOscillatoryIntegral α L}

theorem gap1 (A α₀ : ℝ) (hα₀ : 0 < α₀) :
    |∫ x in (1 : ℝ)..A, Real.cos x| ≤ 2 := by
  have hderiv :
      ∀ x : ℝ, HasDerivAt Real.sin (Real.cos x) x :=
    fun x => Real.hasDerivAt_sin x
  have hint :
      (∫ x in (1 : ℝ)..A, Real.cos x) =
        Real.sin A - Real.sin 1 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x)
      (Real.continuous_cos.intervalIntegrable 1 A)
  rw [hint]
  calc
    |Real.sin A - Real.sin 1| ≤
        |Real.sin A| + |Real.sin 1| := abs_sub _ _
    _ ≤ 1 + 1 :=
      add_le_add (Real.abs_sin_le_one A) (Real.abs_sin_le_one 1)
    _ = 2 := by norm_num

theorem gap2 (α α₀ : ℝ) (hα₀ : 0 < α₀) (hα : α₀ ≤ α) :
    AntitoneOn (fun x : ℝ => 1 / Real.rpow x α) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hαpos : 0 < α := hα₀.trans_le hα
  have hp :=
    Real.rpow_le_rpow (zero_le_one.trans hx) hxy hαpos.le
  exact one_div_le_one_div_of_le
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) α) hp

theorem gap3 (x α α₀ : ℝ) (hα₀ : 0 < α₀) (hα : α₀ ≤ α)
    (hx : 1 ≤ x) :
    0 < 1 / Real.rpow x α := by
  exact one_div_pos.mpr
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) α)

theorem gap4 (x α α₀ : ℝ) (hα₀ : 0 < α₀) (hα : α₀ ≤ α)
    (hx : 1 ≤ x) :
    1 / Real.rpow x α ≤ 1 / Real.rpow x α₀ := by
  have hp :=
    Real.rpow_le_rpow_of_exponent_le hx hα
  exact one_div_le_one_div_of_le
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) α₀) hp

theorem gap5 (x α₀ : ℝ) (hα₀ : 0 < α₀) (hx : 1 ≤ x) :
    0 < 1 / Real.rpow x α₀ := by
  exact one_div_pos.mpr
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) α₀)

theorem gap6 (α α₀ : ℝ) (hα₀ : 0 < α₀) (hα : α₀ ≤ α) :
    Tendsto (fun x : ℝ => 1 / Real.rpow x α) atTop (nhds 0) := by
  have hαpos : 0 < α := hα₀.trans_le hα
  have ht :
      Tendsto (fun x : ℝ => Real.rpow x (-α)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hαpos
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [one_div]
  exact Real.rpow_neg hx.le α

private theorem oscillatory_tail_bound
    (A A₁ α α₀ : ℝ) (hA : 1 < A) (hAA₁ : A < A₁)
    (hα₀ : 0 < α₀) (hα : α₀ ≤ α) :
    |∫ x in A..A₁, integrand α x| ≤
      3 * (1 / Real.rpow A α₀) := by
  have hαpos : 0 < α := hα₀.trans_le hα
  have hApos : 0 < A := zero_lt_one.trans hA
  have hA₁pos : 0 < A₁ := hApos.trans hAA₁
  let u : ℝ → ℝ := fun x => Real.rpow x (-α)
  let u' : ℝ → ℝ := fun x => (-α) * Real.rpow x (-α - 1)
  have hu :
      ∀ x ∈ uIcc A A₁, HasDerivAt u (u' x) x := by
    intro x hx
    rw [uIcc_of_le hAA₁.le] at hx
    have hxpos : 0 < x := hApos.trans_le hx.1
    dsimp [u, u']
    convert Real.hasDerivAt_rpow_const
      (x := x) (p := -α) (Or.inl hxpos.ne') using 1
  have hv :
      ∀ x ∈ uIcc A A₁,
        HasDerivAt Real.sin (Real.cos x) x :=
    fun x _ => Real.hasDerivAt_sin x
  have huInt : IntervalIntegrable u' volume A A₁ := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le hAA₁.le] at hx
    have hxpos : 0 < x := hApos.trans_le hx.1
    dsimp [u']
    exact
      (continuousAt_const.mul
        (continuousAt_id.rpow_const
          (Or.inl hxpos.ne'))).continuousWithinAt
  have hvInt : IntervalIntegrable Real.cos volume A A₁ :=
    Real.continuous_cos.intervalIntegrable A A₁
  have hip :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      hu hv huInt hvInt
  have hleft :
      (∫ x in A..A₁, integrand α x) =
        ∫ x in A..A₁, u x * Real.cos x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hAA₁.le] at hx
    have hxpos : 0 < x := hApos.trans_le hx.1
    rw [integrand, div_eq_mul_inv]
    dsimp [u]
    rw [Real.rpow_neg hxpos.le α]
    ring
  have hformula :
      (∫ x in A..A₁, integrand α x) =
        u A₁ * Real.sin A₁ - u A * Real.sin A -
          ∫ x in A..A₁, u' x * Real.sin x := by
    rw [hleft]
    exact hip
  let major : ℝ → ℝ :=
    fun x => α * Real.rpow x (-α - 1)
  have hmajorInt : IntervalIntegrable major volume A A₁ := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le hAA₁.le] at hx
    have hxpos : 0 < x := hApos.trans_le hx.1
    dsimp [major]
    exact
      (continuousAt_const.mul
        (continuousAt_id.rpow_const
          (Or.inl hxpos.ne'))).continuousWithinAt
  have hmajorValue :
      (∫ x in A..A₁, major x) = u A - u A₁ := by
    have hderiv :
        ∀ x ∈ uIcc A A₁,
          HasDerivAt (fun y : ℝ => -Real.rpow y (-α))
            (major x) x := by
      intro x hx
      rw [uIcc_of_le hAA₁.le] at hx
      have hxpos : 0 < x := hApos.trans_le hx.1
      dsimp [major]
      convert
        (Real.hasDerivAt_rpow_const
          (x := x) (p := -α) (Or.inl hxpos.ne')).neg using 1 <;>
        ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      hderiv hmajorInt]
    dsimp [u]
    ring
  have hrem :
      |∫ x in A..A₁, u' x * Real.sin x| ≤
        u A - u A₁ := by
    have hnorm :
        ‖∫ x in A..A₁, u' x * Real.sin x‖ ≤
          ∫ x in A..A₁, major x := by
      apply intervalIntegral.norm_integral_le_of_norm_le hAA₁.le
      · filter_upwards with x hx
        have hxpos : 0 < x := hApos.trans hx.1
        dsimp [u', major]
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos hαpos,
          abs_of_nonneg (Real.rpow_nonneg hxpos.le (-α - 1))]
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_left
            (mul_le_of_le_one_right
              (Real.rpow_nonneg hxpos.le (-α - 1))
              (Real.abs_sin_le_one x)) hαpos.le)
      · exact hmajorInt
    rw [Real.norm_eq_abs, hmajorValue] at hnorm
    exact hnorm
  have huApos : 0 < u A := by
    dsimp [u]
    exact Real.rpow_pos_of_pos hApos (-α)
  have huA₁nonneg : 0 ≤ u A₁ := by
    dsimp [u]
    exact Real.rpow_nonneg hA₁pos.le (-α)
  have huMono : u A₁ ≤ u A := by
    dsimp [u]
    have hpow :=
      Real.rpow_le_rpow hApos.le hAA₁.le hαpos.le
    rw [Real.rpow_neg hApos.le α, Real.rpow_neg hA₁pos.le α]
    simpa [one_div] using
      (one_div_le_one_div_of_le
        (Real.rpow_pos_of_pos hApos α) hpow)
  have hboundA :
      |u A * Real.sin A| ≤ u A := by
    rw [abs_mul, abs_of_pos huApos]
    exact mul_le_of_le_one_right huApos.le
      (Real.abs_sin_le_one A)
  have hboundA₁ :
      |u A₁ * Real.sin A₁| ≤ u A := by
    calc
      |u A₁ * Real.sin A₁| =
          u A₁ * |Real.sin A₁| := by
        rw [abs_mul, abs_of_nonneg huA₁nonneg]
      _ ≤ u A₁ :=
        mul_le_of_le_one_right huA₁nonneg
          (Real.abs_sin_le_one A₁)
      _ ≤ u A := huMono
  have hremA :
      |∫ x in A..A₁, u' x * Real.sin x| ≤ u A := by
    exact hrem.trans (by linarith)
  rw [hformula]
  have htri :
      |u A₁ * Real.sin A₁ - u A * Real.sin A -
          ∫ x in A..A₁, u' x * Real.sin x| ≤
        |u A₁ * Real.sin A₁| + |u A * Real.sin A| +
          |∫ x in A..A₁, u' x * Real.sin x| := by
    linarith [abs_sub
      (u A₁ * Real.sin A₁) (u A * Real.sin A),
      abs_sub
        (u A₁ * Real.sin A₁ - u A * Real.sin A)
        (∫ x in A..A₁, u' x * Real.sin x)]
  apply htri.trans
  have hsum :
      |u A₁ * Real.sin A₁| + |u A * Real.sin A| +
          |∫ x in A..A₁, u' x * Real.sin x| ≤
        3 * u A := by
    linarith
  apply hsum.trans
  have hcompare := gap4 A α α₀ hα₀ hα hA.le
  dsimp [u]
  rw [Real.rpow_neg hApos.le α]
  simpa [one_div] using
    (mul_le_mul_of_nonneg_left hcompare (by norm_num : (0 : ℝ) ≤ 3))

theorem gap7 (α₀ : ℝ) (hα₀ : 0 < α₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 1 < A₀ ∧
      ∀ A A₁ α : ℝ, A₀ < A → A < A₁ → α₀ ≤ α →
        |∫ x in A..A₁, integrand α x| < ε := by
  have hdecay :
      Tendsto (fun A : ℝ => 3 * (1 / Real.rpow A α₀))
        atTop (𝓝 0) := by
    simpa using
      (gap6 α₀ α₀ hα₀ le_rfl).const_mul 3
  have hevent :
      ∀ᶠ A : ℝ in atTop,
        3 * (1 / Real.rpow A α₀) < ε :=
    (tendsto_order.1 hdecay).2 ε hε
  obtain ⟨A₀, hA₀event⟩ := (eventually_atTop.1 hevent)
  let B₀ : ℝ := max A₀ 2
  refine ⟨B₀, by dsimp [B₀]; linarith [le_max_right A₀ 2], ?_⟩
  intro A A₁ α hBA hAA₁ hα
  have hA : 1 < A := by
    dsimp [B₀] at hBA
    linarith [le_max_right A₀ 2]
  have htail :=
    oscillatory_tail_bound A A₁ α α₀ hA hAA₁ hα₀ hα
  have hsmall : 3 * (1 / Real.rpow A α₀) < ε := by
    apply hA₀event A
    dsimp [B₀] at hBA
    exact (le_max_left A₀ 2).trans hBA.le
  exact htail.trans_lt hsmall

private def J (α : ℝ) : ℝ :=
  ∫ x in Ioi (1 : ℝ),
    Real.sin x * Real.rpow x (-α - 1)

private def G (α : ℝ) : ℝ :=
  -Real.sin 1 + α * J α

private lemma kernel_continuousOn (α : ℝ) :
    ContinuousOn
      (fun x : ℝ => Real.sin x * Real.rpow x (-α - 1))
      (Ioi 1) := by
  intro x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  exact
    (Real.continuous_sin.continuousAt.mul
      (continuousAt_id.rpow_const
        (Or.inl hx0.ne'))).continuousWithinAt

private lemma kernel_integrable {α : ℝ} (hα : 0 < α) :
    IntegrableOn
      (fun x : ℝ => Real.sin x * Real.rpow x (-α - 1))
      (Ioi 1) := by
  have hp :
      IntegrableOn (fun x : ℝ => Real.rpow x (-α - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  apply hp.mono'
  · exact (kernel_continuousOn α).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hrnorm :
        ‖Real.rpow x (-α - 1)‖ = Real.rpow x (-α - 1) :=
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le (-α - 1))
    rw [norm_mul, Real.norm_eq_abs, hrnorm]
    exact mul_le_of_le_one_left
      (Real.rpow_nonneg hx0.le (-α - 1))
      (Real.abs_sin_le_one x)

private lemma kernel_continuousAt_param {α x : ℝ} (hx : 1 < x) :
    ContinuousAt
      (fun a : ℝ => Real.sin x * Real.rpow x (-a - 1)) α := by
  exact continuousAt_const.mul
    (continuousAt_const.rpow
      (continuousAt_id.neg.sub continuousAt_const)
      (Or.inl (zero_lt_one.trans hx).ne'))

private lemma J_continuous :
    ContinuousOn J (Ioi (0 : ℝ)) := by
  intro α hα
  change 0 < α at hα
  let q : ℝ := α / 2
  have hq0 : 0 < q := by
    dsimp [q]
    linarith
  have hqα : q < α := by
    dsimp [q]
    linarith
  let bound : ℝ → ℝ := fun x => Real.rpow x (-q - 1)
  have hbound_int :
      Integrable bound (volume.restrict (Ioi (1 : ℝ))) := by
    exact integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hmeas :
      ∀ᶠ a in 𝓝 α,
        AEStronglyMeasurable
          (fun x : ℝ => Real.sin x * Real.rpow x (-a - 1))
          (volume.restrict (Ioi (1 : ℝ))) := by
    filter_upwards with a
    exact (kernel_continuousOn a).aestronglyMeasurable measurableSet_Ioi
  have hbound :
      ∀ᶠ a in 𝓝 α, ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)),
        ‖Real.sin x * Real.rpow x (-a - 1)‖ ≤ bound x := by
    filter_upwards [Ioi_mem_nhds hqα] with a ha
    change q < a at ha
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hrnorm :
        ‖Real.rpow x (-a - 1)‖ = Real.rpow x (-a - 1) :=
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le (-a - 1))
    rw [norm_mul, Real.norm_eq_abs, hrnorm]
    calc
      |Real.sin x| * Real.rpow x (-a - 1)
          ≤ Real.rpow x (-a - 1) :=
        mul_le_of_le_one_left
          (Real.rpow_nonneg hx0.le (-a - 1))
          (Real.abs_sin_le_one x)
      _ ≤ Real.rpow x (-q - 1) :=
        Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have hcont :
      ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)),
        ContinuousAt
          (fun a : ℝ => Real.sin x * Real.rpow x (-a - 1)) α := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact kernel_continuousAt_param hx
  have H :=
    continuousAt_of_dominated
      (μ := volume.restrict (Ioi (1 : ℝ)))
      hmeas hbound hbound_int hcont
  simpa [J] using H.continuousWithinAt

private lemma finite_formula {α b : ℝ} (hb : 1 < b) :
    (∫ x in (1 : ℝ)..b, integrand α x) =
      Real.rpow b (-α) * Real.sin b - Real.sin 1 +
        α * ∫ x in (1 : ℝ)..b,
          Real.sin x * Real.rpow x (-α - 1) := by
  have hu :
      ∀ x ∈ [[(1 : ℝ), b]],
        HasDerivAt
          (fun y : ℝ => Real.rpow y (-α))
          ((-α) * Real.rpow x (-α - 1)) x := by
    intro x hx
    rw [uIcc_of_le hb.le] at hx
    have hx0 : 0 < x := zero_lt_one.trans_le hx.1
    convert Real.hasDerivAt_rpow_const (x := x) (p := -α)
      (Or.inl hx0.ne') using 1
  have hv :
      ∀ x ∈ [[(1 : ℝ), b]],
        HasDerivAt Real.sin (Real.cos x) x :=
    fun x _ => Real.hasDerivAt_sin x
  have hu_int :
      IntervalIntegrable
        (fun x : ℝ => (-α) * Real.rpow x (-α - 1))
        volume 1 b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le hb.le] at hx
    have hx0 : 0 < x := zero_lt_one.trans_le hx.1
    exact
      (continuousAt_const.mul
        (continuousAt_id.rpow_const
          (Or.inl hx0.ne'))).continuousWithinAt
  have hv_int :
      IntervalIntegrable Real.cos volume 1 b :=
    Real.continuous_cos.intervalIntegrable 1 b
  have hip :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      hu hv hu_int hv_int
  have hleft :
      (∫ x in (1 : ℝ)..b, integrand α x) =
        ∫ x in (1 : ℝ)..b,
          Real.rpow x (-α) * Real.cos x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hb.le] at hx
    have hx0 : 0 ≤ x := zero_le_one.trans hx.1
    have hneg :
        Real.rpow x (-α) = (Real.rpow x α)⁻¹ :=
      Real.rpow_neg hx0 α
    calc
      integrand α x =
          (Real.rpow x α)⁻¹ * Real.cos x := by
        unfold integrand
        rw [div_eq_mul_inv]
        ring
      _ = Real.rpow x (-α) * Real.cos x := by rw [hneg]
  have hrem :
      (∫ x in (1 : ℝ)..b,
          ((-α) * Real.rpow x (-α - 1)) * Real.sin x) =
        (-α) * ∫ x in (1 : ℝ)..b,
          Real.sin x * Real.rpow x (-α - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hleft, hip, hrem]
  have hone : Real.rpow 1 (-α) = 1 := Real.one_rpow (-α)
  rw [hone]
  ring

private lemma boundary_tendsto_zero {α : ℝ} (hα : 0 < α) :
    Tendsto
      (fun b : ℝ => Real.rpow b (-α) * Real.sin b)
      atTop (𝓝 0) := by
  have hp :
      Tendsto (fun b : ℝ => Real.rpow b (-α)) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop hα
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero
    (g := fun b : ℝ => ‖Real.rpow b (-α)‖)
    (fun b => norm_nonneg _) (fun b => ?_)
    (by simpa only [norm_zero] using hp.norm)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (by simpa [Real.norm_eq_abs] using Real.abs_sin_le_one b)

private lemma improper_limit {α : ℝ} (hα : 0 < α) :
    HasOscillatoryIntegral α (G α) := by
  have hkernel :
      Tendsto
        (fun b => ∫ x in (1 : ℝ)..b,
          Real.sin x * Real.rpow x (-α - 1))
        atTop (𝓝 (J α)) := by
    simpa [J] using
      (intervalIntegral_tendsto_integral_Ioi 1
        (kernel_integrable hα) tendsto_id)
  have hlim :
      Tendsto
        (fun b : ℝ =>
          Real.rpow b (-α) * Real.sin b - Real.sin 1 +
            α * ∫ x in (1 : ℝ)..b,
              Real.sin x * Real.rpow x (-α - 1))
        atTop (𝓝 (G α)) := by
    have H :=
      (boundary_tendsto_zero hα).sub_const (Real.sin 1) |>.add
        ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => α) atTop (𝓝 α)).mul hkernel)
    simpa [G] using H
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with b hb
  exact (finite_formula hb).symm

private lemma G_continuous :
    ContinuousOn G (Ioi (0 : ℝ)) := by
  have hJ := J_continuous
  intro α hα
  change
    ContinuousWithinAt
      (fun a : ℝ => -Real.sin 1 + a * J a) (Ioi 0) α
  exact
    continuousWithinAt_const.add
      (continuousWithinAt_id.mul (hJ α hα))

private theorem F_eq_G {α : ℝ} (hα : 0 < α) :
    F α = G α := by
  have hmem : G α ∈ {L : ℝ | HasOscillatoryIntegral α L} :=
    improper_limit hα
  have hsingleton :
      {L : ℝ | HasOscillatoryIntegral α L} = {G α} := by
    ext L
    constructor
    · intro hL
      have heq := tendsto_nhds_unique hL (improper_limit hα)
      simpa only [Set.mem_singleton_iff] using heq
    · intro hL
      simp only [Set.mem_singleton_iff] at hL
      subst L
      exact hmem
  unfold F
  rw [hsingleton]
  simp

theorem gap8 (α₀ : ℝ) (hα₀ : 0 < α₀) :
    ContinuousOn F (Set.Ici α₀) := by
  apply (G_continuous.mono (Ici_subset_Ioi.2 hα₀)).congr
  intro α hα
  exact F_eq_G (hα₀.trans_le hα)

theorem gap9 :
    ContinuousOn F (Set.Ioi 0) := by
  apply G_continuous.congr
  intro α hα
  exact F_eq_G hα

theorem gap10 :
    ContinuousOn F (Set.Ioi 0) := by
  exact gap9

end

end ProofGap.Exercise3780
