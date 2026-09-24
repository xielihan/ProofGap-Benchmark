import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3753

noncomputable section

open Filter MeasureTheory Set
open scoped Interval Topology

def bump (y x : ℝ) : ℝ :=
  Real.exp (-(1 / y ^ 2) * (x - 1 / y) ^ 2)

def gaussian (u : ℝ) : ℝ :=
  Real.exp (-(u ^ 2))

def tail (y A : ℝ) : ℝ :=
  ∫ x in Set.Ioi A, bump y x

def gaussianTail (A : ℝ) : ℝ :=
  ∫ u in Set.Ioi A, gaussian u

def shiftedGaussianTail (y A : ℝ) : ℝ :=
  ∫ x in Set.Ioi A, Real.exp (-((x - 1 / y) ^ 2))

def scaledHalfMass (y : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t ^ 2 / y ^ 2))

def gaussianHalfMass : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), gaussian u

def UniformTail : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ A₀ : ℝ, 1 < A₀ ∧
      ∀ A : ℝ, A₀ < A →
        ∀ y ∈ Set.Ioo (0 : ℝ) 1, tail y A < ε

def Dominates (φ : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 1 ≤ x →
    ∀ y ∈ Set.Ioo (0 : ℝ) 1, bump y x ≤ φ x

def MajorantConverges (φ : ℝ → ℝ) : Prop :=
  (∀ A : ℝ, 1 < A →
    IntervalIntegrable φ volume 1 A) ∧
  ∃ L : ℝ,
    Tendsto (fun A : ℝ => ∫ x in (1 : ℝ)..A, φ x)
      atTop (𝓝 L)

private lemma bump_pos (y x : ℝ) :
    0 < bump y x := Real.exp_pos _

private lemma bump_integrable (y : ℝ) (hy : 0 < y) :
    Integrable (bump y) := by
  have hc : 0 < 1 / y ^ 2 :=
    one_div_pos.mpr (sq_pos_of_pos hy)
  have hg :
      Integrable
        (fun x : ℝ => Real.exp (-(1 / y ^ 2) * x ^ 2)) :=
    integrable_exp_neg_mul_sq hc
  simpa only [bump] using hg.comp_sub_right (1 / y)

private lemma integral_bump_eq (y : ℝ) (hy : 0 < y) :
    (∫ x : ℝ, bump y x) =
      y * Real.sqrt Real.pi := by
  have hshift :=
    integral_sub_right_eq_self
      (μ := volume)
      (fun x : ℝ =>
        Real.exp (-(1 / y ^ 2) * x ^ 2)) (1 / y)
  calc
    (∫ x : ℝ, bump y x) =
        ∫ x : ℝ,
          Real.exp (-(1 / y ^ 2) *
            (x - 1 / y) ^ 2) := by rfl
    _ = ∫ x : ℝ,
          Real.exp (-(1 / y ^ 2) * x ^ 2) := hshift
    _ = Real.sqrt (Real.pi / (1 / y ^ 2)) :=
      integral_gaussian (1 / y ^ 2)
    _ = Real.sqrt (Real.pi * y ^ 2) := by
      congr 1
      field_simp [hy.ne']
    _ = Real.sqrt Real.pi * y := by
      rw [Real.sqrt_mul Real.pi_nonneg,
        Real.sqrt_sq_eq_abs, abs_of_pos hy]
    _ = y * Real.sqrt Real.pi := by ring

private lemma gaussian_pos (x : ℝ) :
    0 < gaussian x := Real.exp_pos _

private lemma gaussian_integrable :
    Integrable gaussian := by
  simpa [gaussian] using
    (integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 by norm_num))

private lemma integral_comp_sub_right_Ioi_shift
    (f : ℝ → ℝ) (a c : ℝ) :
    (∫ x in Ioi a, f (x - c)) =
      ∫ u in Ioi (a - c), f u := by
  have hshift :=
    integral_sub_right_eq_self
      (μ := volume) ((Ioi (a - c)).indicator f) c
  calc
    (∫ x in Ioi a, f (x - c)) =
        ∫ x : ℝ, (Ioi (a - c)).indicator f (x - c) := by
      rw [← integral_indicator measurableSet_Ioi]
      apply MeasureTheory.integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [indicator_apply, mem_Ioi]
        split_ifs with hx₁ hx₂
        · rfl
        · exfalso
          apply hx₂
          linarith
        · exfalso
          apply hx₁
          linarith
        · rfl
    _ = ∫ u : ℝ, (Ioi (a - c)).indicator f u := hshift
    _ = ∫ u in Ioi (a - c), f u := by
      rw [integral_indicator measurableSet_Ioi]

private lemma gaussianTail_tendsto :
    Tendsto gaussianTail atTop (𝓝 0) := by
  have hinterval :
      Tendsto (fun b : ℝ => ∫ x in (0 : ℝ)..b, gaussian x)
        atTop (𝓝 (∫ x in Ioi (0 : ℝ), gaussian x)) :=
    intervalIntegral_tendsto_integral_Ioi 0
      gaussian_integrable.integrableOn tendsto_id
  have hlim :
      Tendsto
        (fun b : ℝ =>
          gaussianTail 0 - ∫ x in (0 : ℝ)..b, gaussian x)
        atTop (𝓝 0) := by
    have hconst :
        Tendsto (fun _ : ℝ => gaussianTail 0) atTop
          (𝓝 (gaussianTail 0)) :=
      tendsto_const_nhds
    have h := hconst.sub hinterval
    simpa [gaussianTail] using h
  have heq :
      (fun b : ℝ => gaussianTail b) =ᶠ[atTop]
        (fun b : ℝ =>
          gaussianTail 0 - ∫ x in (0 : ℝ)..b, gaussian x) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
    have hsplit :=
      intervalIntegral.integral_interval_add_Ioi
        (f := gaussian) (μ := volume) (a := 0) (b := b)
        gaussian_integrable.integrableOn
        gaussian_integrable.integrableOn
    unfold gaussianTail
    linarith
  exact hlim.congr' heq.symm

theorem gap1 :
    ∀ ε : ℝ, 0 < ε →
      ∃ A₀ : ℝ, 1 < A₀ ∧
        gaussianTail (A₀ - Real.sqrt Real.pi / ε) < ε := by
  intro ε hε
  have hev :
      ∀ᶠ B : ℝ in atTop, gaussianTail B < ε :=
    (tendsto_order.1 gaussianTail_tendsto).2 ε hε
  rcases eventually_atTop.1 hev with ⟨T, hT⟩
  let A₀ : ℝ := max 2 (T + Real.sqrt Real.pi / ε)
  refine ⟨A₀, ?_, ?_⟩
  · dsimp [A₀]
    linarith [le_max_left (2 : ℝ)
      (T + Real.sqrt Real.pi / ε)]
  · apply hT
    dsimp [A₀]
    linarith [le_max_right (2 : ℝ)
      (T + Real.sqrt Real.pi / ε)]

theorem gap2 (y A ε : ℝ) (hε : 0 < ε)
    (hylo : ε / Real.sqrt Real.pi ≤ y) (hyhi : y < 1) :
    tail y A < shiftedGaussianTail y A := by
  have hsqrt : 0 < Real.sqrt Real.pi :=
    Real.sqrt_pos.2 Real.pi_pos
  have hy : 0 < y :=
    (div_pos hε hsqrt).trans_le hylo
  have hy2pos : 0 < y ^ 2 := sq_pos_of_pos hy
  have hy2lt : y ^ 2 < 1 := by
    nlinarith
  have hcoef : 1 < 1 / y ^ 2 :=
    one_lt_one_div hy2pos hy2lt
  let g : ℝ → ℝ :=
    fun x => Real.exp (-((x - 1 / y) ^ 2))
  have hgint : Integrable g := by
    simpa [g, gaussian] using
      gaussian_integrable.comp_sub_right (1 / y)
  have hpoint : ∀ x : ℝ, bump y x ≤ g x := by
    intro x
    unfold bump
    dsimp [g]
    apply Real.exp_le_exp.mpr
    have hz : 0 ≤ (x - 1 / y) ^ 2 := sq_nonneg _
    have hm :=
      mul_le_mul_of_nonneg_right hcoef.le hz
    nlinarith
  have hstrict :
      ∀ x : ℝ, x ≠ 1 / y → bump y x < g x := by
    intro x hx
    unfold bump
    dsimp [g]
    apply Real.exp_lt_exp.mpr
    have hz : 0 < (x - 1 / y) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
    have hm :=
      mul_lt_mul_of_pos_right hcoef hz
    nlinarith
  let B : ℝ := max A (1 / y) + 1
  have hsubset :
      Ioo B (B + 1) ⊆
        Function.support (fun x => g x - bump y x) ∩ Ioi A := by
    intro x hx
    constructor
    · have hxcenter : x ≠ 1 / y := by
        intro hxy
        have hcenterB : 1 / y < B := by
          dsimp [B]
          linarith [le_max_right A (1 / y)]
        linarith [hx.1]
      exact (sub_pos.mpr (hstrict x hxcenter)).ne'
    · have hAB : A < B := by
        dsimp [B]
        linarith [le_max_left A (1 / y)]
      exact hAB.trans hx.1
  have hvolume :
      0 < volume (Ioo B (B + 1)) := by
    simp [Real.volume_Ioo]
  have hsupp :
      0 <
        volume
          (Function.support (fun x => g x - bump y x) ∩ Ioi A) :=
    hvolume.trans_le (measure_mono hsubset)
  have hdiffint :
      IntegrableOn (fun x => g x - bump y x) (Ioi A) :=
    (hgint.sub (bump_integrable y hy)).integrableOn
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Ioi A)]
        (fun x => g x - bump y x) :=
    Eventually.of_forall fun x => sub_nonneg.mpr (hpoint x)
  have hpos :
      0 < ∫ x in Ioi A, g x - bump y x :=
    (setIntegral_pos_iff_support_of_nonneg_ae
      hnonneg hdiffint).2 hsupp
  rw [integral_sub hgint.integrableOn
    (bump_integrable y hy).integrableOn] at hpos
  change (∫ x in Ioi A, bump y x) < ∫ x in Ioi A, g x
  exact sub_pos.mp hpos

theorem gap3 (y A : ℝ) (hy : y ≠ 0) :
    shiftedGaussianTail y A = gaussianTail (A - 1 / y) := by
  unfold shiftedGaussianTail gaussianTail
  simpa [gaussian] using
    integral_comp_sub_right_Ioi_shift gaussian A (1 / y)

theorem gap4 (y A ε : ℝ) (hε : 0 < ε)
    (hylo : ε / Real.sqrt Real.pi ≤ y) (hyhi : y < 1) :
    tail y A < gaussianTail (A - 1 / y) := by
  have hsqrt : 0 < Real.sqrt Real.pi :=
    Real.sqrt_pos.2 Real.pi_pos
  have hy : y ≠ 0 :=
    ne_of_gt ((div_pos hε hsqrt).trans_le hylo)
  rw [← gap3 y A hy]
  exact gap2 y A ε hε hylo hyhi

theorem gap5 (y A ε : ℝ) (hε : 0 < ε)
    (hylo : ε / Real.sqrt Real.pi ≤ y) :
    gaussianTail (A - 1 / y) ≤
      gaussianTail (A - Real.sqrt Real.pi / ε) := by
  have hsqrt : 0 < Real.sqrt Real.pi :=
    Real.sqrt_pos.2 Real.pi_pos
  have hδ : 0 < ε / Real.sqrt Real.pi :=
    div_pos hε hsqrt
  have hy : 0 < y := hδ.trans_le hylo
  have hrecip :
      1 / y ≤ Real.sqrt Real.pi / ε := by
    have :=
      one_div_le_one_div_of_le hδ hylo
    calc
      1 / y ≤ 1 / (ε / Real.sqrt Real.pi) := this
      _ = Real.sqrt Real.pi / ε := by
        field_simp [hε.ne', hsqrt.ne']
  apply setIntegral_mono_set
  · exact gaussian_integrable.integrableOn
  · exact Eventually.of_forall fun x => (gaussian_pos x).le
  · exact
      (Ioi_subset_Ioi
        (by linarith : A - Real.sqrt Real.pi / ε ≤ A - 1 / y)).eventuallyLE

theorem gap6 (A A₀ ε : ℝ) (hA : A₀ < A) :
    gaussianTail (A - Real.sqrt Real.pi / ε) <
      gaussianTail (A₀ - Real.sqrt Real.pi / ε) := by
  let a : ℝ := A₀ - Real.sqrt Real.pi / ε
  let b : ℝ := A - Real.sqrt Real.pi / ε
  have hab : a < b := by
    dsimp [a, b]
    linarith
  have hsplit :=
    intervalIntegral.integral_interval_add_Ioi
      (f := gaussian) (μ := volume) (a := a) (b := b)
      gaussian_integrable.integrableOn
      gaussian_integrable.integrableOn
  have hpos :
      0 < ∫ x in a..b, gaussian x :=
    intervalIntegral.intervalIntegral_pos_of_pos
      gaussian_integrable.intervalIntegrable gaussian_pos hab
  unfold gaussianTail
  dsimp [a, b] at hsplit
  linarith

theorem gap7 (A₀ ε : ℝ)
    (hsmall : gaussianTail (A₀ - Real.sqrt Real.pi / ε) < ε) :
    gaussianTail (A₀ - Real.sqrt Real.pi / ε) < ε := by
  exact hsmall

theorem gap8 (y A A₀ ε : ℝ) (hε : 0 < ε)
    (hylo : ε / Real.sqrt Real.pi ≤ y) (hyhi : y < 1)
    (hA : A₀ < A)
    (hsmall : gaussianTail (A₀ - Real.sqrt Real.pi / ε) < ε) :
    gaussianTail (A - 1 / y) < ε := by
  exact
    (gap5 y A ε hε hylo).trans_lt
      ((gap6 A A₀ ε hA).trans hsmall)

theorem gap9 (y A ε : ℝ) (hε : 0 < ε) (hy : 0 < y)
    (hysmall : y < ε / Real.sqrt Real.pi) (hA : 1 < A) :
    tail y A < tail y 1 := by
  have hint := bump_integrable y hy
  have hsplit :=
    intervalIntegral.integral_interval_add_Ioi
      (f := bump y) (μ := volume) (a := 1) (b := A)
      hint.integrableOn hint.integrableOn
  have hpos :
      0 < ∫ x in (1 : ℝ)..A, bump y x :=
    intervalIntegral.intervalIntegral_pos_of_pos
      hint.intervalIntegrable (bump_pos y) hA
  unfold tail
  linarith

theorem gap10 (y : ℝ) (hy : 0 < y) (hy1 : y < 1) :
    tail y 1 =
      (∫ t in (0 : ℝ)..(1 / y - 1),
        Real.exp (-(t ^ 2 / y ^ 2))) +
      scaledHalfMass y := by
  let q : ℝ → ℝ :=
    fun t => Real.exp (-(t ^ 2 / y ^ 2))
  have hcenter : 1 < 1 / y :=
    one_lt_one_div hy hy1
  have hbumpRight :
      bump y = fun x => q (x - 1 / y) := by
    funext x
    unfold bump
    dsimp [q]
    congr 2
    field_simp [hy.ne']
  have hbumpLeft :
      bump y = fun x => q (1 / y - x) := by
    funext x
    unfold bump
    dsimp [q]
    congr 2
    field_simp [hy.ne']
    <;> ring
  have hleft :
      (∫ x in (1 : ℝ)..(1 / y), bump y x) =
        ∫ t in (0 : ℝ)..(1 / y - 1), q t := by
    rw [hbumpLeft]
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (f := q) (a := (1 : ℝ)) (b := 1 / y) (1 / y))
  have hright :
      tail y (1 / y) = scaledHalfMass y := by
    unfold tail scaledHalfMass
    rw [hbumpRight]
    simpa [q] using
      integral_comp_sub_right_Ioi_shift q (1 / y) (1 / y)
  have hsplit :=
    intervalIntegral.integral_interval_add_Ioi
      (f := bump y) (μ := volume)
      (a := (1 : ℝ)) (b := 1 / y)
      (bump_integrable y hy).integrableOn
      (bump_integrable y hy).integrableOn
  unfold tail at hright
  unfold tail at hsplit ⊢
  rw [hleft, hright] at hsplit
  simpa [q] using hsplit.symm

theorem gap11 (y : ℝ) (hy : 0 < y) (hy1 : y < 1) :
    tail y 1 < 2 * scaledHalfMass y := by
  let q : ℝ → ℝ :=
    fun t => Real.exp (-(t ^ 2 / y ^ 2))
  have hqint : Integrable q := by
    have hc : 0 < 1 / y ^ 2 :=
      one_div_pos.mpr (sq_pos_of_pos hy)
    have hint :=
      integrable_exp_neg_mul_sq hc
    have hq :
        q =
          fun t : ℝ =>
            Real.exp (-(1 / y ^ 2) * t ^ 2) := by
      funext t
      dsimp [q]
      congr 2
      ring
    rw [hq]
    exact hint
  have hu : 0 < 1 / y - 1 := by
    linarith [one_lt_one_div hy hy1]
  have htailpos :
      0 < ∫ t in Ioi (1 / y - 1), q t := by
    apply
      (setIntegral_pos_iff_support_of_nonneg_ae
        (Eventually.of_forall fun t => (Real.exp_pos _).le)
        hqint.integrableOn).2
    have hsupport : Function.support q = univ := by
      ext t
      simp [q, Function.mem_support]
    rw [hsupport, univ_inter]
    simp
  have hsplit :=
    intervalIntegral.integral_interval_add_Ioi
      (f := q) (μ := volume)
      (a := (0 : ℝ)) (b := 1 / y - 1)
      hqint.integrableOn hqint.integrableOn
  have hleft :
      (∫ t in (0 : ℝ)..(1 / y - 1),
        Real.exp (-(t ^ 2 / y ^ 2))) <
        scaledHalfMass y := by
    unfold scaledHalfMass
    dsimp [q] at hsplit htailpos
    linarith
  rw [gap10 y hy hy1]
  linarith

theorem gap12 (y : ℝ) (hy : 0 < y) :
    2 * scaledHalfMass y = 2 * y * gaussianHalfMass := by
  have hchange :=
    integral_comp_mul_right_Ioi gaussian 0
      (one_div_pos.mpr hy)
  have hfun :
      (fun t : ℝ => Real.exp (-(t ^ 2 / y ^ 2))) =
        (fun t : ℝ => gaussian (t * (1 / y))) := by
    funext t
    unfold gaussian
    congr 2
    field_simp [hy.ne']
  have hmass :
      scaledHalfMass y = y * gaussianHalfMass := by
    rw [scaledHalfMass, hfun]
    simpa [gaussianHalfMass, zero_mul, inv_inv,
      smul_eq_mul, hy.ne'] using hchange
  rw [hmass]
  ring

theorem gap13 :
    gaussianHalfMass = Real.sqrt Real.pi / 2 := by
  simpa [gaussianHalfMass, gaussian] using
    (integral_gaussian_Ioi (1 : ℝ))

theorem gap14 (y ε : ℝ) (hε : 0 < ε) (hy : 0 < y)
    (hysmall : y < ε / Real.sqrt Real.pi) :
    2 * y * (Real.sqrt Real.pi / 2) < ε := by
  have hsqrt : 0 < Real.sqrt Real.pi :=
    Real.sqrt_pos.2 Real.pi_pos
  have hmul :=
    mul_lt_mul_of_pos_right hysmall hsqrt
  field_simp [hsqrt.ne'] at hmul ⊢
  nlinarith

theorem gap15 (y ε : ℝ) (hε : 0 < ε) (hy : 0 < y)
    (hy1 : y < 1) (hysmall : y < ε / Real.sqrt Real.pi) :
    tail y 1 < ε := by
  calc
    tail y 1 < 2 * scaledHalfMass y :=
      gap11 y hy hy1
    _ = 2 * y * gaussianHalfMass :=
      gap12 y hy
    _ = 2 * y * (Real.sqrt Real.pi / 2) := by
      rw [gap13]
    _ < ε :=
      gap14 y ε hε hy hysmall

theorem gap16 (ε A₀ : ℝ) (hε : 0 < ε) (hA₀ : 1 < A₀)
    (hsmall : gaussianTail (A₀ - Real.sqrt Real.pi / ε) < ε) :
    ∀ A : ℝ, A₀ < A →
      ∀ y ∈ Set.Ioo (0 : ℝ) 1, tail y A < ε := by
  intro A hA y hy
  by_cases hylo : ε / Real.sqrt Real.pi ≤ y
  · exact
      (gap4 y A ε hε hylo hy.2).trans
        (gap8 y A A₀ ε hε hylo hy.2 hA hsmall)
  · have hysmall : y < ε / Real.sqrt Real.pi :=
      lt_of_not_ge hylo
    exact
      (gap9 y A ε hε hy.1 hysmall (hA₀.trans hA)).trans
        (gap15 y ε hε hy.1 hy.2 hysmall)

theorem gap17 :
    UniformTail := by
  intro ε hε
  rcases gap1 ε hε with ⟨A₀, hA₀, hsmall⟩
  exact ⟨A₀, hA₀, gap16 ε A₀ hε hA₀ hsmall⟩

theorem gap18 (φ : ℝ → ℝ)
    (hdom : Dominates φ) (hconv : MajorantConverges φ) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ φ x₀ < 1 := by
  by_contra hnone
  push_neg at hnone
  rcases hconv.2 with ⟨L, hL⟩
  have hup :
      ∀ᶠ b : ℝ in atTop,
        (∫ x in (1 : ℝ)..b, φ x) < L + 1 :=
    (tendsto_order.1 hL).2 (L + 1) (by linarith)
  rcases
      (hup.and
        (eventually_gt_atTop (max 1 (L + 3)))).exists with
    ⟨b, hbup, hb⟩
  have hb1lt : 1 < b := by
    linarith [le_max_left (1 : ℝ) (L + 3)]
  have hb1 : 1 ≤ b := hb1lt.le
  have hlower :
      (∫ x in (1 : ℝ)..b, (1 : ℝ)) ≤
        ∫ x in (1 : ℝ)..b, φ x := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hb1
    · exact Continuous.intervalIntegrable continuous_const 1 b
    · exact hconv.1 b hb1lt
    · intro x hx
      exact hnone x hx.1
  simp only [intervalIntegral.integral_const,
    smul_eq_mul, mul_one] at hlower
  linarith [le_max_right (1 : ℝ) (L + 3)]

theorem gap19 (x₀ : ℝ) (hx₀ : 1 < x₀) :
    0 < 1 / x₀ := by
  exact one_div_pos.mpr (zero_lt_one.trans hx₀)

theorem gap20 (x₀ : ℝ) (hx₀ : 1 < x₀) :
    1 / x₀ < 1 := by
  have hx0 : 0 < x₀ := zero_lt_one.trans hx₀
  exact (div_lt_iff₀ hx0).2 (by simpa using hx₀)

theorem gap21 :
    (0 : ℝ) < 1 := by
  exact zero_lt_one

theorem gap22 (x₀ : ℝ) (hx₀ : 1 < x₀) :
    bump (1 / x₀) x₀ = 1 := by
  have hx0 : 0 < x₀ := zero_lt_one.trans hx₀
  unfold bump
  field_simp [hx0.ne']
  simp

theorem gap23 (φ : ℝ → ℝ)
    (hdom : Dominates φ) (hconv : MajorantConverges φ) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ 1 > φ x₀ := by
  exact gap18 φ hdom hconv

theorem gap24 (φ : ℝ → ℝ) (x₀ : ℝ)
    (hx₀ : 1 < x₀) (hφ : φ x₀ < 1) :
    bump (1 / x₀) x₀ > φ x₀ := by
  rw [gap22 x₀ hx₀]
  exact hφ

theorem gap25 (φ : ℝ → ℝ) :
    Dominates φ ∧ MajorantConverges φ → False := by
  rintro ⟨hdom, hconv⟩
  rcases gap18 φ hdom hconv with ⟨x₀, hx₀, hφ⟩
  have hy : 1 / x₀ ∈ Ioo (0 : ℝ) 1 :=
    ⟨gap19 x₀ hx₀, gap20 x₀ hx₀⟩
  have hmajor := hdom x₀ hx₀.le (1 / x₀) hy
  have hb := gap22 x₀ hx₀
  rw [hb] at hmajor
  linarith

theorem gap26 (φ : ℝ → ℝ) :
    Dominates φ → ¬ MajorantConverges φ := by
  intro hdom hconv
  exact gap25 φ ⟨hdom, hconv⟩

end

end ProofGap.Exercise3753
