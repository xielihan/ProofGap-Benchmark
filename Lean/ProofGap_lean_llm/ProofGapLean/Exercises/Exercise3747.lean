import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
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

namespace ProofGap.Exercise3747

noncomputable section

open Filter Set
open scoped BigOperators Interval Topology

def integrand (a x : ℝ) : ℝ :=
  Real.cos x / (x + a)

def partialIntegral (a A : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..A, integrand a x

def Converges (a : ℝ) : Prop :=
  (∀ A : ℝ, 0 < A →
    IntervalIntegrable (integrand a) MeasureTheory.volume 0 A) ∧
  ∃ L : ℝ, Tendsto (partialIntegral a) atTop (𝓝 L)

def exceptionalParameter (n : ℕ) : ℝ :=
  -(((n : ℝ) + 1 / 2) * Real.pi)

def tailPartialIntegral (A : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..A, Real.cos t / (t + Real.pi / 2)

def singularPartial (a δ ε : ℝ) : ℝ :=
  ∫ x in -a + ε..-a + δ, integrand a x

private lemma integrand_continuousOn_nonneg
    (a : ℝ) (ha : 0 < a) :
    ContinuousOn (integrand a) (Set.Ici 0) := by
  intro x hx
  unfold integrand
  have hx0 : 0 ≤ x := hx
  have hden : x + a ≠ 0 := by
    intro h
    linarith
  simpa only [Pi.div_apply, Pi.add_apply, id_eq] using
    (Real.continuous_cos.continuousAt.div
      (continuousAt_id.add continuousAt_const)
      hden).continuousWithinAt

private lemma integrand_intervalIntegrable_nonneg
    (a : ℝ) (ha : 0 < a) (u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    IntervalIntegrable (integrand a)
      MeasureTheory.volume u v := by
  apply ContinuousOn.intervalIntegrable
  apply (integrand_continuousOn_nonneg a ha).mono
  intro x hx
  rw [Set.mem_uIcc] at hx
  rcases hx with hx | hx
  · exact hu.trans hx.1
  · exact hv.trans hx.1

private lemma integration_by_parts
    (a u v : ℝ) (ha : 0 < a)
    (hu : 0 ≤ u) (huv : u ≤ v) :
    (∫ x in u..v, integrand a x) =
      Real.sin v / (v + a) - Real.sin u / (u + a) +
        ∫ x in u..v, Real.sin x / (x + a) ^ 2 := by
  let F : ℝ → ℝ := fun x => Real.sin x / (x + a)
  have hderiv :
      ∀ x ∈ Set.uIcc u v,
        HasDerivAt F
          (integrand a x - Real.sin x / (x + a) ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le huv] at hx
    have hden : x + a ≠ 0 := by
      intro h
      linarith [hx.1]
    have hq := Real.hasDerivAt_sin x |>.div
      ((hasDerivAt_id x).add_const a)
      hden
    convert hq using 1
    dsimp [integrand]
    field_simp [hden]
  have hint :
      IntervalIntegrable
        (fun x =>
          integrand a x - Real.sin x / (x + a) ^ 2)
        MeasureTheory.volume u v := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le huv] at hx
    have hden : x + a ≠ 0 := by
      intro h
      linarith [hu, hx.1]
    have hcos :
        ContinuousAt (integrand a) x := by
      unfold integrand
      simpa only [Pi.div_apply, Pi.add_apply, id_eq] using
        Real.continuous_cos.continuousAt.div
          (continuousAt_id.add continuousAt_const) hden
    have hsin :
        ContinuousAt
          (fun y => Real.sin y / (y + a) ^ 2) x := by
      simpa only [Pi.div_apply, Pi.add_apply, id_eq] using
        Real.continuous_sin.continuousAt.div
          ((continuousAt_id.add continuousAt_const).pow 2)
          (pow_ne_zero 2 hden)
    exact (hcos.sub hsin).continuousWithinAt
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      hderiv hint
  have hcos :=
    integrand_intervalIntegrable_nonneg a ha u v hu
      (hu.trans huv)
  have hsin :
      IntervalIntegrable
        (fun x => Real.sin x / (x + a) ^ 2)
        MeasureTheory.volume u v := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hden : x + a ≠ 0 := by
      rw [Set.uIcc_of_le huv] at hx
      intro h
      linarith [hx.1]
    exact (Real.continuous_sin.continuousAt.div
      ((continuousAt_id.add continuousAt_const).pow 2)
      (pow_ne_zero 2 hden)).continuousWithinAt
  rw [intervalIntegral.integral_sub hcos hsin] at hFTC
  dsimp [F] at hFTC
  linarith

theorem gap1 (a u v : ℝ) (ha : 0 < a) (hu : 0 ≤ u) (huv : u ≤ v) :
    (∫ x in u..v, integrand a x) =
      Real.sin v / (v + a) - Real.sin u / (u + a) +
        ∫ x in u..v, Real.sin x / (x + a) ^ 2 := by
  exact integration_by_parts a u v ha hu huv

theorem gap2 (a : ℝ) (ha : 0 < a) (s : ℕ → ℝ)
    (hs0 : s 0 = 0) (hsmono : StrictMono s)
    (hstop : Tendsto s atTop atTop) (m p : ℕ) :
    (∑ j ∈ Finset.range p,
        (∫ x in s (m + j)..s (m + j + 1), integrand a x)) =
      Real.sin (s (m + p)) / (s (m + p) + a) -
        Real.sin (s m) / (s m + a) +
        ∫ x in s m..s (m + p), Real.sin x / (x + a) ^ 2 := by
  have hsnonneg : ∀ k : ℕ, 0 ≤ s k := by
    intro k
    rw [← hs0]
    exact hsmono.monotone (Nat.zero_le k)
  have hsum :
      (∑ j ∈ Finset.range p,
          (∫ x in s (m + j)..s (m + j + 1),
            integrand a x)) =
        ∫ x in s m..s (m + p), integrand a x := by
    have h :=
      intervalIntegral.sum_integral_adjacent_intervals
        (f := integrand a)
        (a := fun j : ℕ => s (m + j))
        (n := p)
        (fun j hj =>
          integrand_intervalIntegrable_nonneg a ha
            (s (m + j)) (s (m + (j + 1)))
            (hsnonneg _) (hsnonneg _))
    simpa [Nat.add_assoc] using h
  rw [hsum]
  exact gap1 a (s m) (s (m + p)) ha
    (hsnonneg m)
    (hsmono.monotone (Nat.le_add_right m p))

private lemma integral_inv_sq_add
    (a u v : ℝ) (ha : 0 < a)
    (hu : 0 ≤ u) (huv : u ≤ v) :
    (∫ x in u..v, 1 / (x + a) ^ 2) =
      1 / (u + a) - 1 / (v + a) := by
  let F : ℝ → ℝ := fun x => -(x + a)⁻¹
  have hderiv :
      ∀ x ∈ Set.uIcc u v,
        HasDerivAt F (1 / (x + a) ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le huv] at hx
    have hden : x + a ≠ 0 := by
      intro h
      linarith [hu, hx.1]
    have h :=
      (((hasDerivAt_id x).add_const a).inv hden).neg
    convert h using 1
    dsimp
    field_simp [hden]
  have hint :
      IntervalIntegrable (fun x => 1 / (x + a) ^ 2)
        MeasureTheory.volume u v := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le huv] at hx
    have hden : x + a ≠ 0 := by
      intro h
      linarith [hu, hx.1]
    exact (continuousAt_const.div
      ((continuousAt_id.add continuousAt_const).pow 2)
      (pow_ne_zero 2 hden)).continuousWithinAt
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      hderiv hint
  simpa [F, one_div, sub_eq_add_neg, add_comm] using hFTC

theorem gap3 (a : ℝ) (ha : 0 < a) (s : ℕ → ℝ)
    (hs0 : s 0 = 0) (hsmono : StrictMono s)
    (hstop : Tendsto s atTop atTop) (m p : ℕ) :
    |∑ j ∈ Finset.range p,
        (∫ x in s (m + j)..s (m + j + 1), integrand a x)| ≤
      2 / (s m + a) := by
  have hsnonneg : ∀ k : ℕ, 0 ≤ s k := by
    intro k
    rw [← hs0]
    exact hsmono.monotone (Nat.zero_le k)
  have hsle : s m ≤ s (m + p) :=
    hsmono.monotone (Nat.le_add_right m p)
  let u : ℝ := s m
  let v : ℝ := s (m + p)
  let I : ℝ :=
    ∫ x in u..v, Real.sin x / (x + a) ^ 2
  have hu : 0 ≤ u := hsnonneg m
  have hv : 0 ≤ v := hu.trans hsle
  have huv : u ≤ v := hsle
  have hEq := gap2 a ha s hs0 hsmono hstop m p
  have huDen : 0 < u + a := by linarith
  have hvDen : 0 < v + a := by linarith
  have hEu :
      |Real.sin u / (u + a)| ≤ 1 / (u + a) := by
    rw [abs_div, abs_of_pos huDen]
    exact div_le_div_of_nonneg_right
      (Real.abs_sin_le_one u) huDen.le
  have hEv :
      |Real.sin v / (v + a)| ≤ 1 / (v + a) := by
    rw [abs_div, abs_of_pos hvDen]
    exact div_le_div_of_nonneg_right
      (Real.abs_sin_le_one v) hvDen.le
  have hsinInt :
      IntervalIntegrable
        (fun x => Real.sin x / (x + a) ^ 2)
        MeasureTheory.volume u v := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le huv] at hx
    have hden : x + a ≠ 0 := by
      intro h
      linarith [hu, hx.1]
    exact (Real.continuous_sin.continuousAt.div
      ((continuousAt_id.add continuousAt_const).pow 2)
      (pow_ne_zero 2 hden)).continuousWithinAt
  have hmajInt :
      IntervalIntegrable
        (fun x => 1 / (x + a) ^ 2)
        MeasureTheory.volume u v := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le huv] at hx
    have hden : x + a ≠ 0 := by
      intro h
      linarith [hu, hx.1]
    exact (continuousAt_const.div
      ((continuousAt_id.add continuousAt_const).pow 2)
      (pow_ne_zero 2 hden)).continuousWithinAt
  have hpoint :
      ∀ x ∈ Set.Icc u v,
        |Real.sin x / (x + a) ^ 2| ≤
          1 / (x + a) ^ 2 := by
    intro x hx
    have hdenpos : 0 < x + a := by
      linarith [hu, hx.1]
    rw [abs_div, abs_of_nonneg (sq_nonneg (x + a))]
    exact div_le_div_of_nonneg_right
      (Real.abs_sin_le_one x) (sq_nonneg (x + a))
  have hI :
      |I| ≤ 1 / (u + a) - 1 / (v + a) := by
    calc
      |I| ≤
          ∫ x in u..v,
            |Real.sin x / (x + a) ^ 2| :=
        intervalIntegral.abs_integral_le_integral_abs huv
      _ ≤ ∫ x in u..v, 1 / (x + a) ^ 2 :=
        intervalIntegral.integral_mono_on huv
          hsinInt.norm hmajInt hpoint
      _ = 1 / (u + a) - 1 / (v + a) :=
        integral_inv_sq_add a u v ha hu huv
  rw [hEq]
  change
    |Real.sin v / (v + a) -
        Real.sin u / (u + a) + I| ≤
      2 / (u + a)
  calc
    |Real.sin v / (v + a) -
        Real.sin u / (u + a) + I| ≤
        |Real.sin v / (v + a)| +
          |Real.sin u / (u + a)| + |I| := by
      calc
        |Real.sin v / (v + a) -
            Real.sin u / (u + a) + I| ≤
            |Real.sin v / (v + a) -
              Real.sin u / (u + a)| + |I| :=
          abs_add_le _ _
        _ ≤
            (|Real.sin v / (v + a)| +
              |Real.sin u / (u + a)|) + |I| :=
          add_le_add (abs_sub _ _) le_rfl
    _ ≤ 2 / (u + a) := by
      have htwo :
          2 / (u + a) =
            1 / (u + a) + 1 / (u + a) := by
        ring
      rw [htwo]
      linarith

private lemma correction_integrableOn_Ioi
    (a : ℝ) (ha : 0 < a) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => Real.sin x / (x + a) ^ 2)
      (Set.Ioi 0) := by
  have hmajor :
      MeasureTheory.IntegrableOn
        (fun x : ℝ => Real.rpow (x + a) (-2 : ℝ))
        (Set.Ioi 0) := by
    exact integrableOn_add_rpow_Ioi_of_lt
      (a := (-2 : ℝ)) (c := (0 : ℝ)) (m := a)
      (by norm_num) (by linarith)
  refine hmajor.mono' ?_ ?_
  · have hcont :
        ContinuousOn
          (fun x : ℝ => Real.sin x / (x + a) ^ 2)
          (Set.Ioi 0) := by
      intro x hx
      have hx0 : 0 < x := hx
      have hden : x + a ≠ 0 := by
        intro h
        linarith
      exact (Real.continuous_sin.continuousAt.div
        ((continuousAt_id.add continuousAt_const).pow 2)
        (pow_ne_zero 2 hden)).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards
      [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with x hx
    have hx0 : 0 < x := hx
    have hxpa : 0 < x + a := by linarith
    have hrpow :
        Real.rpow (x + a) (-2 : ℝ) =
          1 / (x + a) ^ 2 := by
      calc
        Real.rpow (x + a) (-2 : ℝ) =
            (x + a) ^ (-2 : ℤ) := by
          convert Real.rpow_intCast (x + a) (-2) using 1 <;>
            norm_num
        _ = 1 / (x + a) ^ 2 := by
          simp [one_div]
          rfl
    rw [Real.norm_eq_abs, abs_div,
      abs_of_nonneg (sq_nonneg (x + a)), hrpow]
    exact div_le_div_of_nonneg_right
      (Real.abs_sin_le_one x) (sq_nonneg (x + a))

private lemma boundary_tendsto_zero
    (a : ℝ) :
    Tendsto
      (fun A : ℝ => Real.sin A / (A + a))
      atTop (𝓝 0) := by
  have hden :
      Tendsto (fun A : ℝ => A + a) atTop atTop := by
    simpa [add_comm] using
      (tendsto_const_nhds.add_atTop tendsto_id :
        Tendsto (fun A : ℝ => a + A) atTop atTop)
  exact tendsto_bdd_div_atTop_nhds_zero
    (Filter.Eventually.of_forall Real.neg_one_le_sin)
    (Filter.Eventually.of_forall Real.sin_le_one)
    hden

theorem gap4 (a : ℝ) (ha : 0 < a) :
    Converges a := by
  constructor
  · intro A hA
    exact integrand_intervalIntegrable_nonneg a ha 0 A
      (by norm_num) hA.le
  · let C : ℝ :=
      ∫ x : ℝ in Set.Ioi 0,
        Real.sin x / (x + a) ^ 2
    refine ⟨C, ?_⟩
    have hcorr :=
      correction_integrableOn_Ioi a ha
    have htail :
        Tendsto
          (fun A : ℝ =>
            ∫ x in (0 : ℝ)..A,
              Real.sin x / (x + a) ^ 2)
          atTop (𝓝 C) := by
      simpa [C] using
        (MeasureTheory.intervalIntegral_tendsto_integral_Ioi
          0 hcorr tendsto_id)
    have hsum :=
      (boundary_tendsto_zero a).add htail
    have hsum' :
        Tendsto
          (fun A : ℝ =>
            Real.sin A / (A + a) +
              ∫ x in (0 : ℝ)..A,
                Real.sin x / (x + a) ^ 2)
          atTop (𝓝 C) := by
      simpa using hsum
    apply hsum'.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with A hA
    have hparts := gap1 a 0 A ha (by norm_num) hA
    simpa [partialIntegral] using hparts.symm

private lemma cos_div_intervalIntegrable_pos
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable
      (fun x : ℝ => Real.cos x / x)
      MeasureTheory.volume u v := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [Set.mem_uIcc] at hx
  have hx0 : x ≠ 0 := by
    rcases hx with hx | hx
    · exact ne_of_gt (hu.trans_le hx.1)
    · exact ne_of_gt (hv.trans_le hx.1)
  exact (Real.continuous_cos.continuousAt.div
    continuousAt_id hx0).continuousWithinAt

private lemma cos_div_near_zero_tendsto_atTop :
    Tendsto
      (fun A : ℝ =>
        ∫ x in A..Real.pi / 2, Real.cos x / x)
      (𝓝[>] (0 : ℝ)) atTop := by
  let d : ℝ := Real.pi / 3
  let C : ℝ :=
    ∫ x in d..Real.pi / 2, Real.cos x / x
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hdb : d < Real.pi / 2 := by
    dsimp [d]
    nlinarith [Real.pi_pos]
  have hlower :
      Tendsto
        (fun A : ℝ =>
          (1 / 2 : ℝ) * Real.log (d / A) + C)
        (𝓝[>] (0 : ℝ)) atTop := by
    have hdiv :
        Tendsto (fun A : ℝ => d / A)
          (𝓝[>] (0 : ℝ)) atTop := by
      have h :=
        Filter.Tendsto.pos_mul_atTop hd
          tendsto_const_nhds
          (tendsto_inv_nhdsGT_zero :
            Tendsto (fun A : ℝ => A⁻¹)
              (𝓝[>] (0 : ℝ)) atTop)
      simpa [div_eq_mul_inv] using h
    have hlog :
        Tendsto (fun A : ℝ => Real.log (d / A))
          (𝓝[>] (0 : ℝ)) atTop :=
      Real.tendsto_log_atTop.comp hdiv
    have hhalf :
        Tendsto
          (fun A : ℝ =>
            (1 / 2 : ℝ) * Real.log (d / A))
          (𝓝[>] (0 : ℝ)) atTop :=
      hlog.const_mul_atTop (by norm_num)
    simpa [add_comm] using
      (tendsto_const_nhds.add_atTop hhalf :
        Tendsto
          (fun A : ℝ =>
            C + (1 / 2 : ℝ) * Real.log (d / A))
          (𝓝[>] (0 : ℝ)) atTop)
  apply tendsto_atTop_mono'
    (𝓝[>] (0 : ℝ)) ?_ hlower
  filter_upwards [Ioo_mem_nhdsGT hd] with A hA
  have hAδ :
      IntervalIntegrable
        (fun x : ℝ => Real.cos x / x)
        MeasureTheory.volume A d :=
    cos_div_intervalIntegrable_pos A d hA.1 hd
  have hδb :
      IntervalIntegrable
        (fun x : ℝ => Real.cos x / x)
        MeasureTheory.volume d (Real.pi / 2) :=
    cos_div_intervalIntegrable_pos d (Real.pi / 2)
      hd (by positivity)
  have hInv :
      IntervalIntegrable
        (fun x : ℝ => (1 / 2 : ℝ) * (1 / x))
        MeasureTheory.volume A d := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hA.2.le] at hx
    have hx0 : x ≠ 0 :=
      ne_of_gt (hA.1.trans_le hx.1)
    exact
      (continuousAt_const.mul
        (continuousAt_const.div continuousAt_id hx0)).continuousWithinAt
  have hpoint :
      ∀ x ∈ Set.Icc A d,
        (1 / 2 : ℝ) * (1 / x) ≤ Real.cos x / x := by
    intro x hx
    have hx0 : 0 < x := hA.1.trans_le hx.1
    have hdpi : d ≤ Real.pi := by
      dsimp [d]
      nlinarith [Real.pi_pos]
    have hcos :
        (1 / 2 : ℝ) ≤ Real.cos x := by
      have h :=
        Real.cos_le_cos_of_nonneg_of_le_pi
          hx0.le hdpi hx.2
      simpa [d, Real.cos_pi_div_three] using h
    have hdiv :=
      div_le_div_of_nonneg_right hcos hx0.le
    simpa [mul_div_assoc] using hdiv
  have hmono :
      (1 / 2 : ℝ) * Real.log (d / A) ≤
        ∫ x in A..d, Real.cos x / x := by
    calc
      (1 / 2 : ℝ) * Real.log (d / A) =
          ∫ x in A..d, (1 / 2 : ℝ) * (1 / x) := by
        rw [intervalIntegral.integral_const_mul,
          integral_one_div_of_pos hA.1 hd]
      _ ≤ ∫ x in A..d, Real.cos x / x :=
        intervalIntegral.integral_mono_on hA.2.le
          hInv hAδ hpoint
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals
      hAδ hδb
  dsimp [C]
  rw [← hsplit]
  linarith

theorem gap5 :
    ¬ ∃ L : ℝ,
      Tendsto
        (fun A : ℝ =>
          ∫ x in A..Real.pi / 2, Real.cos x / x)
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  rintro ⟨L, hL⟩
  exact
    (not_tendsto_nhds_of_tendsto_atTop
      cos_div_near_zero_tendsto_atTop L) hL

private lemma exceptional_tail_identity (n : ℕ) (t : ℝ) :
    integrand (exceptionalParameter n)
        (((n : ℝ) + 1) * Real.pi + t) =
      (-1 : ℝ) ^ (n + 1) *
        (Real.cos t / (t + Real.pi / 2)) := by
  unfold integrand exceptionalParameter
  have harg :
      ((n : ℝ) + 1) * Real.pi + t =
        t + ((n + 1 : ℕ) : ℝ) * Real.pi := by
    push_cast
    ring
  rw [harg, Real.cos_add_nat_mul_pi]
  push_cast
  ring

private lemma exceptional_singular_cos_identity
    (n : ℕ) (x : ℝ) :
    Real.cos x =
      (-1 : ℝ) ^ (n + 1) *
        Real.sin
          (x - (((n : ℝ) + 1 / 2) * Real.pi)) := by
  let t : ℝ :=
    x - (((n : ℝ) + 1 / 2) * Real.pi)
  have harg :
      x =
        (t + (n : ℝ) * Real.pi) + Real.pi / 2 := by
    dsimp [t]
    ring
  rw [harg, Real.cos_add_pi_div_two,
    Real.sin_add_nat_mul_pi, pow_succ]
  ring

private lemma exceptional_integrand_eq_sinc
    (n : ℕ) (x : ℝ)
    (hx :
      x ≠ ((n : ℝ) + 1 / 2) * Real.pi) :
    integrand (exceptionalParameter n) x =
      (-1 : ℝ) ^ (n + 1) *
        Real.sinc
          (x - (((n : ℝ) + 1 / 2) * Real.pi)) := by
  have ht :
      x - (((n : ℝ) + 1 / 2) * Real.pi) ≠ 0 :=
    sub_ne_zero.mpr hx
  unfold integrand
  rw [exceptional_singular_cos_identity n x]
  unfold exceptionalParameter
  rw [Real.sinc, if_neg ht]
  congr 1
  ring

private lemma exceptional_intervalIntegrable
    (n : ℕ) (u v : ℝ) :
    IntervalIntegrable
      (integrand (exceptionalParameter n))
      MeasureTheory.volume u v := by
  let c : ℝ :=
    ((n : ℝ) + 1 / 2) * Real.pi
  let g : ℝ → ℝ :=
    fun x =>
      (-1 : ℝ) ^ (n + 1) * Real.sinc (x - c)
  have hg :
      IntervalIntegrable g MeasureTheory.volume u v := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      (Real.continuous_sinc.comp
        (continuous_id.sub continuous_const))
  have hae :
      g =ᵐ[MeasureTheory.volume]
        integrand (exceptionalParameter n) := by
    filter_upwards
      [MeasureTheory.volume.ae_ne c] with x hx
    symm
    simpa [g, c] using
      exceptional_integrand_eq_sinc n x hx
  constructor
  · exact hg.1.congr
      (MeasureTheory.ae_restrict_of_ae hae)
  · exact hg.2.congr
      (MeasureTheory.ae_restrict_of_ae hae)

private lemma exceptional_tail_integral_identity
    (n : ℕ) (A : ℝ) :
    (∫ x in ((n : ℝ) + 1) * Real.pi..A,
        integrand (exceptionalParameter n) x) =
      (-1 : ℝ) ^ (n + 1) *
        tailPartialIntegral
          (A - ((n : ℝ) + 1) * Real.pi) := by
  let B : ℝ := ((n : ℝ) + 1) * Real.pi
  have hchange :=
    intervalIntegral.integral_comp_add_right
      (f := integrand (exceptionalParameter n))
      (a := (0 : ℝ)) (b := A - B) B
  calc
    (∫ x in ((n : ℝ) + 1) * Real.pi..A,
        integrand (exceptionalParameter n) x) =
        ∫ t in (0 : ℝ)..A - B,
          integrand (exceptionalParameter n) (t + B) := by
      simpa [B] using hchange.symm
    _ = ∫ t in (0 : ℝ)..A - B,
          (-1 : ℝ) ^ (n + 1) *
            (Real.cos t / (t + Real.pi / 2)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simpa [B, add_comm] using
        exceptional_tail_identity n t
    _ = (-1 : ℝ) ^ (n + 1) *
          tailPartialIntegral (A - B) := by
      rw [intervalIntegral.integral_const_mul]
      rfl
    _ = (-1 : ℝ) ^ (n + 1) *
          tailPartialIntegral
            (A - ((n : ℝ) + 1) * Real.pi) := by
      rfl

theorem gap6 (a : ℝ) (n : ℕ) (ha : a = exceptionalParameter n) :
    ∃ L T : ℝ,
      Tendsto (partialIntegral a) atTop (𝓝 L) ∧
      Tendsto tailPartialIntegral atTop (𝓝 T) ∧
      L =
        (∫ x in (0 : ℝ)..((n : ℝ) + 1) * Real.pi, integrand a x) +
          (-1 : ℝ) ^ (n + 1) * T := by
  subst a
  have htailConv := gap4 (Real.pi / 2) (by positivity)
  rcases htailConv.2 with ⟨T, hT⟩
  have hT' :
      Tendsto tailPartialIntegral atTop (𝓝 T) := by
    simpa [tailPartialIntegral, partialIntegral, integrand] using hT
  let B : ℝ := ((n : ℝ) + 1) * Real.pi
  let J : ℝ :=
    ∫ x in (0 : ℝ)..B,
      integrand (exceptionalParameter n) x
  let L : ℝ := J + (-1 : ℝ) ^ (n + 1) * T
  refine ⟨L, T, ?_, hT', ?_⟩
  · have hshift :
        Tendsto (fun A : ℝ => A - B) atTop atTop := by
      simpa [sub_eq_add_neg, add_comm] using
        (tendsto_const_nhds.add_atTop tendsto_id :
          Tendsto (fun A : ℝ => -B + A) atTop atTop)
    have hshiftTail :
        Tendsto
          (fun A : ℝ => tailPartialIntegral (A - B))
          atTop (𝓝 T) :=
      hT'.comp hshift
    have hscaled :
        Tendsto
          (fun A : ℝ =>
            (-1 : ℝ) ^ (n + 1) *
              tailPartialIntegral (A - B))
          atTop
          (𝓝 ((-1 : ℝ) ^ (n + 1) * T)) :=
      tendsto_const_nhds.mul hshiftTail
    have hsum :
        Tendsto
          (fun A : ℝ =>
            J + (-1 : ℝ) ^ (n + 1) *
              tailPartialIntegral (A - B))
          atTop (𝓝 L) := by
      simpa [L] using tendsto_const_nhds.add hscaled
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop B] with A hA
    have h0B :=
      exceptional_intervalIntegrable n 0 B
    have hBA :=
      exceptional_intervalIntegrable n B A
    have hsplit :=
      intervalIntegral.integral_add_adjacent_intervals
        h0B hBA
    have htailEq :=
      exceptional_tail_integral_identity n A
    dsimp [partialIntegral, J]
    rw [← hsplit, htailEq]
  · rfl

theorem gap7 (n : ℕ) :
    Converges (exceptionalParameter n) := by
  constructor
  · intro A hA
    exact exceptional_intervalIntegrable n 0 A
  · rcases gap6 (exceptionalParameter n) n rfl with
      ⟨L, T, hL, hT, hEq⟩
    exact ⟨L, hL⟩

theorem gap8 (a : ℝ) (ha : a < 0)
    (hnexc : ∀ n : ℕ, a ≠ exceptionalParameter n) :
    Real.cos (-a) ≠ 0 := by
  intro hcos
  rcases Real.cos_eq_zero_iff.mp hcos with ⟨k, hk⟩
  have hk0 : 0 ≤ k := by
    by_contra hnot
    have hkle : k ≤ -1 := by omega
    have hkleR : (k : ℝ) ≤ -1 := by
      exact_mod_cast hkle
    have hpos : 0 < -a := by linarith
    rw [hk] at hpos
    nlinarith [Real.pi_pos]
  apply hnexc k.toNat
  have hkNat :
      ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hk0
  unfold exceptionalParameter
  rw [hkNat]
  calc
    a = -(-a) := by ring
    _ = -((2 * (k : ℝ) + 1) * Real.pi / 2) := by
      rw [hk]
    _ = -(((k : ℝ) + 1 / 2) * Real.pi) := by
      ring

private lemma local_cos_close
    (c : ℝ) (hc : Real.cos c ≠ 0) :
    ∃ d : ℝ, 0 < d ∧
      ∀ t ∈ Set.Icc (0 : ℝ) d,
        |Real.cos (c + t) - Real.cos c| <
          |Real.cos c| / 2 := by
  let S : Set ℝ :=
    {t |
      |Real.cos (c + t) - Real.cos c| <
        |Real.cos c| / 2}
  have hSopen : IsOpen S := by
    dsimp [S]
    apply isOpen_lt
    · fun_prop
    · fun_prop
  have hzero : (0 : ℝ) ∈ S := by
    dsimp [S]
    simp only [add_zero, sub_self, abs_zero]
    exact half_pos (abs_pos.mpr hc)
  rcases (Metric.isOpen_iff.mp hSopen 0 hzero) with
    ⟨r, hr, hball⟩
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro t ht
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, sub_zero,
    abs_of_nonneg ht.1]
  exact ht.2.trans_lt (half_lt_self hr)

private lemma singular_change_variables
    (a δ ε : ℝ) :
    singularPartial a δ ε =
      ∫ t in ε..δ, Real.cos (-a + t) / t := by
  have hchange :=
    intervalIntegral.integral_comp_add_right
      (f := integrand a) (a := ε) (b := δ) (-a)
  unfold singularPartial
  calc
    (∫ x in -a + ε..-a + δ, integrand a x) =
        ∫ t in ε..δ, integrand a (t + -a) := by
      simpa [add_comm] using hchange.symm
    _ = ∫ t in ε..δ, Real.cos (-a + t) / t := by
      apply intervalIntegral.integral_congr
      intro t ht
      change Real.cos (t + -a) / (t + -a + a) =
        Real.cos (-a + t) / t
      rw [show t + -a + a = t by ring,
        show t + -a = -a + t by ring]

theorem gap9 (a : ℝ) (ha : a < 0)
    (hnexc : ∀ n : ℕ, a ≠ exceptionalParameter n) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ δ ∈ Set.Ioc (0 : ℝ) δ₀, ∀ ε ∈ Set.Ioo (0 : ℝ) δ,
        |singularPartial a δ ε| ≥
          (1 / 2 : ℝ) * |Real.cos (-a)| * Real.log (δ / ε) := by
  have hcos : Real.cos (-a) ≠ 0 :=
    gap8 a ha hnexc
  rcases local_cos_close (-a) hcos with
    ⟨d, hd, hclose⟩
  refine ⟨d, hd, ?_⟩
  intro δ hδ ε hε
  let C : ℝ := Real.cos (-a)
  let q : ℝ := |C| / 2
  have hqpos : 0 < q := by
    dsimp [q, C]
    exact half_pos (abs_pos.mpr hcos)
  have hfunInt :
      IntervalIntegrable
        (fun t : ℝ => Real.cos (-a + t) / t)
        MeasureTheory.volume ε δ := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hε.2.le] at ht
    have ht0 : t ≠ 0 :=
      ne_of_gt (hε.1.trans_le ht.1)
    exact ((Real.continuous_cos.comp
      (continuous_const.add continuous_id)).continuousAt.div
        continuousAt_id ht0).continuousWithinAt
  have hInvInt :
      IntervalIntegrable (fun t : ℝ => 1 / t)
        MeasureTheory.volume ε δ := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hε.2.le] at ht
    have ht0 : t ≠ 0 :=
      ne_of_gt (hε.1.trans_le ht.1)
    exact
      (continuousAt_const.div continuousAt_id ht0).continuousWithinAt
  have hqInt :
      IntervalIntegrable (fun t : ℝ => q * (1 / t))
        MeasureTheory.volume ε δ :=
    hInvInt.const_mul q
  have hqIntegral :
      (∫ t in ε..δ, q * (1 / t)) =
        q * Real.log (δ / ε) := by
    rw [intervalIntegral.integral_const_mul,
      integral_one_div_of_pos hε.1 hδ.1]
  rw [singular_change_variables]
  have hcoef :
      (1 / 2 : ℝ) * |Real.cos (-a)| *
          Real.log (δ / ε) =
        q * Real.log (δ / ε) := by
    dsimp [q, C]
    ring
  rw [hcoef]
  have hCne : C ≠ 0 := by
    simpa only [C] using hcos
  rcases lt_or_gt_of_ne hCne with hCneg | hCpos
  · have hpoint :
        ∀ t ∈ Set.Icc ε δ,
          Real.cos (-a + t) / t ≤
            -q * (1 / t) := by
      intro t ht
      have htpos : 0 < t := hε.1.trans_le ht.1
      have hcl :=
        hclose t
          ⟨htpos.le, ht.2.trans hδ.2⟩
      change
        |Real.cos (-a + t) - C| < |C| / 2 at hcl
      have hCabs : |C| = -C := abs_of_neg hCneg
      have hupper :
          Real.cos (-a + t) ≤ -q := by
        have hdif := (abs_lt.mp hcl).2
        dsimp [q]
        rw [hCabs]
        linarith
      have hdiv :=
        div_le_div_of_nonneg_right hupper htpos.le
      calc
        Real.cos (-a + t) / t ≤ (-q) / t := hdiv
        _ = -q * (1 / t) := by ring
    have hnegInt :
        IntervalIntegrable
          (fun t : ℝ => -q * (1 / t))
          MeasureTheory.volume ε δ :=
      hInvInt.const_mul (-q)
    have hmono :
        (∫ t in ε..δ, Real.cos (-a + t) / t) ≤
          ∫ t in ε..δ, -q * (1 / t) :=
      intervalIntegral.integral_mono_on hε.2.le
        hfunInt hnegInt hpoint
    have hnegEq :
        (∫ t in ε..δ, -q * (1 / t)) =
          -(q * Real.log (δ / ε)) := by
      rw [intervalIntegral.integral_const_mul,
        integral_one_div_of_pos hε.1 hδ.1]
      ring
    rw [hnegEq] at hmono
    exact le_trans (by linarith)
      (neg_le_abs
        (∫ t in ε..δ, Real.cos (-a + t) / t))
  · have hpoint :
        ∀ t ∈ Set.Icc ε δ,
          q * (1 / t) ≤
            Real.cos (-a + t) / t := by
      intro t ht
      have htpos : 0 < t := hε.1.trans_le ht.1
      have hcl :=
        hclose t
          ⟨htpos.le, ht.2.trans hδ.2⟩
      change
        |Real.cos (-a + t) - C| < |C| / 2 at hcl
      have hCabs : |C| = C := abs_of_pos hCpos
      have hlower :
          q ≤ Real.cos (-a + t) := by
        have hdif := (abs_lt.mp hcl).1
        dsimp [q]
        rw [hCabs]
        linarith
      have hdiv :=
        div_le_div_of_nonneg_right hlower htpos.le
      calc
        q * (1 / t) = q / t := by ring
        _ ≤ Real.cos (-a + t) / t := hdiv
    have hmono :
        (∫ t in ε..δ, q * (1 / t)) ≤
          ∫ t in ε..δ, Real.cos (-a + t) / t :=
      intervalIntegral.integral_mono_on hε.2.le
        hqInt hfunInt hpoint
    rw [hqIntegral] at hmono
    exact hmono.trans
      (le_abs_self
        (∫ t in ε..δ, Real.cos (-a + t) / t))

theorem gap10 (a δ : ℝ) (ha : a < 0)
    (hcos : Real.cos (-a) ≠ 0) (hδ : 0 < δ) :
    Tendsto
      (fun ε : ℝ =>
        (1 / 2 : ℝ) * |Real.cos (-a)| * Real.log (δ / ε))
      (𝓝[>] (0 : ℝ)) atTop := by
  have hdiv :
      Tendsto (fun ε : ℝ => δ / ε)
        (𝓝[>] (0 : ℝ)) atTop := by
    have h :=
      Filter.Tendsto.pos_mul_atTop hδ
        tendsto_const_nhds
        (tendsto_inv_nhdsGT_zero :
          Tendsto (fun ε : ℝ => ε⁻¹)
            (𝓝[>] (0 : ℝ)) atTop)
    simpa [div_eq_mul_inv] using h
  have hlog :
      Tendsto (fun ε : ℝ => Real.log (δ / ε))
        (𝓝[>] (0 : ℝ)) atTop :=
    Real.tendsto_log_atTop.comp hdiv
  have hcoef :
      0 < (1 / 2 : ℝ) * |Real.cos (-a)| :=
    mul_pos (by norm_num) (abs_pos.mpr hcos)
  exact hlog.const_mul_atTop hcoef

theorem gap11 (a : ℝ) (ha : a < 0)
    (hnexc : ∀ n : ℕ, a ≠ exceptionalParameter n) :
    ∃ δ : ℝ, 0 < δ ∧
      Tendsto (fun ε : ℝ => |singularPartial a δ ε|)
        (𝓝[>] (0 : ℝ)) atTop := by
  rcases gap9 a ha hnexc with ⟨δ, hδ, hbound⟩
  refine ⟨δ, hδ, ?_⟩
  have hlower :=
    gap10 a δ ha (gap8 a ha hnexc) hδ
  apply tendsto_atTop_mono'
    (𝓝[>] (0 : ℝ)) ?_ hlower
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  exact hbound δ ⟨hδ, le_rfl⟩ ε hε

theorem gap12 (a : ℝ) (ha : a < 0)
    (hnexc : ∀ n : ℕ, a ≠ exceptionalParameter n) :
    ¬ Converges a := by
  intro hconv
  rcases gap11 a ha hnexc with
    ⟨d, hd, hAtTop⟩
  let c : ℝ := -a
  let b : ℝ := c + d
  have hc : 0 < c := by
    dsimp [c]
    linarith
  have hcb : c ≤ b := by
    dsimp [b]
    linarith
  have hb : 0 < b := hc.trans_le hcb
  have h0b :
      IntervalIntegrable (integrand a)
        MeasureTheory.volume 0 b :=
    hconv.1 b hb
  have hsub :
      IntervalIntegrable (integrand a)
        MeasureTheory.volume c b := by
    apply h0b.mono_set
    rw [Set.uIcc_of_le hcb,
      Set.uIcc_of_le hb.le]
    intro x hx
    exact ⟨hc.le.trans hx.1, hx.2⟩
  have hright :
      ContinuousOn
        (fun x : ℝ =>
          ∫ t in b..x, integrand a t)
        (Set.uIcc c b) :=
    intervalIntegral.continuousOn_primitive_interval'
      hsub Set.right_mem_uIcc
  have hleft :
      ContinuousOn
        (fun x : ℝ =>
          ∫ t in x..b, integrand a t)
        (Set.uIcc c b) := by
    have heq :
        (fun x : ℝ =>
          ∫ t in x..b, integrand a t) =
        (fun x : ℝ =>
          -(∫ t in b..x, integrand a t)) := by
      funext x
      exact intervalIntegral.integral_symm b x
    rw [heq]
    exact hright.neg
  have hshiftNhds :
      Tendsto (fun ε : ℝ => c + ε)
        (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    have hzero :
        Tendsto (fun ε : ℝ => ε)
          (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      (tendsto_id :
        Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0))
        |>.mono_left inf_le_left
    simpa using tendsto_const_nhds.add hzero
  have hmem :
      ∀ᶠ ε : ℝ in (𝓝[>] (0 : ℝ)),
        c + ε ∈ Set.uIcc c b := by
    filter_upwards [Ioc_mem_nhdsGT hd] with ε hε
    rw [Set.uIcc_of_le hcb]
    constructor
    · exact le_add_of_nonneg_right hε.1.le
    · simpa [b] using add_le_add_left hε.2 c
  have hshift :
      Tendsto (fun ε : ℝ => c + ε)
        (𝓝[>] (0 : ℝ)) (𝓝[Set.uIcc c b] c) :=
    tendsto_nhdsWithin_iff.2 ⟨hshiftNhds, hmem⟩
  have hfiniteRaw :
      Tendsto
        (fun ε : ℝ =>
          ∫ t in c + ε..b, integrand a t)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ t in c..b, integrand a t)) :=
    (hleft c Set.left_mem_uIcc).tendsto.comp hshift
  have hfinite :
      Tendsto
        (fun ε : ℝ => |singularPartial a d ε|)
        (𝓝[>] (0 : ℝ))
        (𝓝 |∫ t in c..b, integrand a t|) := by
    have hnorm := hfiniteRaw.norm
    simpa [singularPartial, c, b, Real.norm_eq_abs] using hnorm
  exact
    (not_tendsto_nhds_of_tendsto_atTop
      hAtTop |∫ t in c..b, integrand a t|) hfinite

private lemma not_converges_zero :
    ¬ Converges 0 := by
  intro hconv
  let b : ℝ := Real.pi / 2
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hint :
      IntervalIntegrable
        (fun x : ℝ => Real.cos x / x)
        MeasureTheory.volume 0 b := by
    have h := hconv.1 b hb
    change
      IntervalIntegrable
        (fun x : ℝ => Real.cos x / (x + 0))
        MeasureTheory.volume 0 b at h
    simpa only [add_zero] using h
  have hright :
      ContinuousOn
        (fun x : ℝ =>
          ∫ t in b..x, Real.cos t / t)
        (Set.uIcc (0 : ℝ) b) :=
    intervalIntegral.continuousOn_primitive_interval'
      hint Set.right_mem_uIcc
  have hleft :
      ContinuousOn
        (fun x : ℝ =>
          ∫ t in x..b, Real.cos t / t)
        (Set.uIcc (0 : ℝ) b) := by
    have heq :
        (fun x : ℝ =>
          ∫ t in x..b, Real.cos t / t) =
        (fun x : ℝ =>
          -(∫ t in b..x, Real.cos t / t)) := by
      funext x
      exact intervalIntegral.integral_symm b x
    rw [heq]
    exact hright.neg
  have hmem :
      ∀ᶠ x : ℝ in (𝓝[>] (0 : ℝ)),
        x ∈ Set.uIcc (0 : ℝ) b := by
    filter_upwards [Ioc_mem_nhdsGT hb] with x hx
    rw [Set.uIcc_of_le hb.le]
    exact ⟨hx.1.le, hx.2⟩
  have hshift :
      Tendsto (fun x : ℝ => x)
        (𝓝[>] (0 : ℝ))
        (𝓝[Set.uIcc (0 : ℝ) b] 0) :=
    tendsto_nhdsWithin_iff.2
      ⟨((tendsto_id :
          Tendsto (fun x : ℝ => x)
            (𝓝 0) (𝓝 0)).mono_left inf_le_left),
        hmem⟩
  have hfinite :
      Tendsto
        (fun A : ℝ =>
          ∫ x in A..Real.pi / 2, Real.cos x / x)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ x in (0 : ℝ)..Real.pi / 2,
          Real.cos x / x)) := by
    simpa [b] using
      (hleft 0 Set.left_mem_uIcc).tendsto.comp hshift
  exact gap5
    ⟨(∫ x in (0 : ℝ)..Real.pi / 2,
      Real.cos x / x), hfinite⟩

theorem gap13 (a : ℝ) :
    (0 < a ∨ ∃ n : ℕ, a = exceptionalParameter n) ↔ Converges a := by
  constructor
  · rintro (ha | ⟨n, hn⟩)
    · exact gap4 a ha
    · rw [hn]
      exact gap7 n
  · intro hconv
    by_cases ha : 0 < a
    · exact Or.inl ha
    · have hnonpos : a ≤ 0 := le_of_not_gt ha
      rcases hnonpos.eq_or_lt with hzero | hneg
      · subst a
        exact False.elim (not_converges_zero hconv)
      · by_cases hex :
          ∃ n : ℕ, a = exceptionalParameter n
        · exact Or.inr hex
        · have hnexc :
              ∀ n : ℕ, a ≠ exceptionalParameter n := by
            intro n hn
            exact hex ⟨n, hn⟩
          exact False.elim (gap12 a hneg hnexc hconv)

end

end ProofGap.Exercise3747
