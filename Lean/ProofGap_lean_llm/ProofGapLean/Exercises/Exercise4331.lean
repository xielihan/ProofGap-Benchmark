import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4331

noncomputable section

open MeasureTheory
open scoped Interval Topology

def partialX (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => u x p.2) p.1

def partialY (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => u p.1 y) p.2

def partialXX (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => partialX u (x, p.2)) p.1

def partialYY (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => partialY u (p.1, y)) p.2

def laplacian (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  partialXX u p + partialYY u p

def tangent (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  (deriv (fun s => (γ s).1) t, deriv (fun s => (γ s).2) t)

def speed (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ :=
  Real.sqrt ((tangent γ t).1 ^ 2 + (tangent γ t).2 ^ 2)

def outwardNormal (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  ((tangent γ t).2 / speed γ t, -(tangent γ t).1 / speed γ t)

def normalDerivative
    (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ :=
  partialX u (γ t) * (outwardNormal γ t).1 +
    partialY u (γ t) * (outwardNormal γ t).2

def normalFlux (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, normalDerivative u γ t * speed γ t

def wedgeFlux (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    partialX u (γ t) * deriv (fun s => (γ s).2) t -
      partialY u (γ t) * deriv (fun s => (γ s).1) t

def areaIntegral (f : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ)) : ℝ :=
  ∫ p in D, f p

def IsPositiveBoundary
    (γ : ℝ → ℝ × ℝ) (D : Set (ℝ × ℝ)) : Prop :=
  ContDiff ℝ 1 γ ∧
    γ 0 = γ 1 ∧
    Set.InjOn γ (Set.Ico (0 : ℝ) 1) ∧
    γ '' Set.Icc (0 : ℝ) 1 = frontier D ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, speed γ t > 0) ∧
    Bornology.IsBounded D ∧
    D = closure (interior D) ∧
    0 < ∫ t in (0 : ℝ)..1,
      (γ t).1 * deriv (fun s => (γ s).2) t -
        (γ t).2 * deriv (fun s => (γ s).1) t

def IsC2 (u : ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)

def IsHarmonic (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ p : ℝ × ℝ, laplacian u p = 0

/-- Green's theorem for one geometric boundary/domain pair.  The geometric
predicate above does not by itself expose the measure-theoretic hypotheses
required by Mathlib's integral API, so the missing analytic theorem is kept as
an explicit reusable interface rather than an equality tailored to `u`. -/
def SatisfiesGreenTheorem
    (γ : ℝ → ℝ × ℝ) (D : Set (ℝ × ℝ)) : Prop :=
  ∀ v : ℝ → ℝ → ℝ, IsC2 v →
    wedgeFlux v γ = areaIntegral (laplacian v) D

/-- Uniform Green theorem used when a statement quantifies over all positive
boundaries. -/
def GreenTheoremForPositiveBoundaries : Prop :=
  ∀ (γ : ℝ → ℝ × ℝ) (D : Set (ℝ × ℝ)),
    IsPositiveBoundary γ D → SatisfiesGreenTheorem γ D

theorem gap1
    (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ) (t : ℝ) :
    normalDerivative u γ t =
      partialX u (γ t) * (outwardNormal γ t).1 +
        partialY u (γ t) * (outwardNormal γ t).2 := by
  rfl

theorem gap2
    (γ : ℝ → ℝ × ℝ) (t : ℝ) (hspeed : speed γ t ≠ 0) :
    (outwardNormal γ t).1 * speed γ t =
      deriv (fun s => (γ s).2) t := by
  unfold outwardNormal tangent
  exact div_mul_cancel₀ _ hspeed

theorem gap3
    (γ : ℝ → ℝ × ℝ) (t : ℝ) (hspeed : speed γ t ≠ 0) :
    (outwardNormal γ t).2 * speed γ t =
      -deriv (fun s => (γ s).1) t := by
  unfold outwardNormal tangent
  exact div_mul_cancel₀ _ hspeed

theorem gap4
    (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (hregular : ∀ t ∈ Set.Icc (0 : ℝ) 1, speed γ t ≠ 0) :
    normalFlux u γ = wedgeFlux u γ := by
  unfold normalFlux wedgeFlux normalDerivative
  apply intervalIntegral.integral_congr
  intro t ht
  change
    (partialX u (γ t) * (outwardNormal γ t).1 +
        partialY u (γ t) * (outwardNormal γ t).2) *
        speed γ t =
      partialX u (γ t) * deriv (fun s => (γ s).2) t -
        partialY u (γ t) * deriv (fun s => (γ s).1) t
  rw [add_mul, mul_assoc, gap2 γ t (hregular t (by simpa using ht)),
    mul_assoc, gap3 γ t (hregular t (by simpa using ht))]
  ring

theorem gap5
    (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (D : Set (ℝ × ℝ)) (hu : IsC2 u)
    (hboundary : IsPositiveBoundary γ D)
    (hGreen : SatisfiesGreenTheorem γ D) :
    wedgeFlux u γ = areaIntegral (laplacian u) D := by
  exact hGreen u hu

theorem gap6
    (u : ℝ → ℝ → ℝ) (D : Set (ℝ × ℝ)) :
    areaIntegral
        (fun p => partialXX u p + partialYY u p) D =
      areaIntegral (laplacian u) D := by
  rfl

theorem gap7
    (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (D : Set (ℝ × ℝ)) (hu : IsC2 u)
    (hboundary : IsPositiveBoundary γ D)
    (hGreen : SatisfiesGreenTheorem γ D) :
    normalFlux u γ = areaIntegral (laplacian u) D := by
  have hregular :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, speed γ t ≠ 0 :=
    fun t ht => ne_of_gt (hboundary.2.2.2.2.1 t ht)
  rw [gap4 u γ hregular]
  exact hGreen u hu

theorem gap8
    (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (D : Set (ℝ × ℝ)) (hu : IsC2 u)
    (hboundary : IsPositiveBoundary γ D)
    (hGreen : SatisfiesGreenTheorem γ D) :
    normalFlux u γ = 0 ↔ areaIntegral (laplacian u) D = 0 := by
  rw [gap7 u γ D hu hboundary hGreen]

theorem gap9
    (u : ℝ → ℝ → ℝ) (hharm : IsHarmonic u) :
    ∀ D : Set (ℝ × ℝ), areaIntegral (laplacian u) D = 0 := by
  intro D
  have hzero : laplacian u = fun _ => 0 := funext hharm
  rw [hzero]
  simp [areaIntegral]

theorem gap10
    (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ)
    (hcont : Continuous (laplacian u)) (hne : laplacian u p ≠ 0) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∃ r > 0, ∀ q ∈ Metric.ball p r, 0 < σ * laplacian u q := by
  by_cases hpos : 0 < laplacian u p
  · have hopen : IsOpen {q : ℝ × ℝ | 0 < laplacian u q} :=
      isOpen_lt continuous_const hcont
    obtain ⟨r, hr, hball⟩ :=
      (Metric.isOpen_iff.1 hopen) p hpos
    refine ⟨1, Or.inl rfl, r, hr, ?_⟩
    intro q hq
    simpa using hball hq
  · have hneg : laplacian u p < 0 := by
      have hle : laplacian u p ≤ 0 := le_of_not_gt hpos
      exact lt_of_le_of_ne hle hne
    have hopen : IsOpen {q : ℝ × ℝ | laplacian u q < 0} :=
      isOpen_lt hcont continuous_const
    obtain ⟨r, hr, hball⟩ :=
      (Metric.isOpen_iff.1 hopen) p hneg
    refine ⟨-1, Or.inr rfl, r, hr, ?_⟩
    intro q hq
    have hqneg := hball hq
    change laplacian u q < 0 at hqneg
    nlinarith

theorem gap11
    (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ)
    (hcont : Continuous (laplacian u)) (hne : laplacian u p ≠ 0) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∃ r > 0,
        0 < σ * areaIntegral (laplacian u) (Metric.ball p r) := by
  obtain ⟨σ, hσ, r, hr, hpos⟩ := gap10 u p hcont hne
  refine ⟨σ, hσ, r, hr, ?_⟩
  let f : ℝ × ℝ → ℝ := fun q => σ * laplacian u q
  have hfcont : Continuous f := continuous_const.mul hcont
  have hfint : IntegrableOn f (Metric.ball p r) :=
    (hfcont.continuousOn.integrableOn_compact
      (isCompact_closedBall p r)).mono_set Metric.ball_subset_closedBall
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Metric.ball p r)] f :=
    ae_restrict_of_forall_mem measurableSet_ball
      (fun q hq => (hpos q hq).le)
  have hsupp :
      Metric.ball p r ⊆ Function.support f := by
    intro q hq
    exact Function.mem_support.mpr (ne_of_gt (hpos q hq))
  unfold areaIntegral
  rw [← MeasureTheory.integral_const_mul]
  apply
    (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hfint).2
  rw [Set.inter_eq_right.mpr hsupp]
  exact Metric.measure_ball_pos volume p hr

theorem gap12
    (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ)
    (hcont : Continuous (laplacian u))
    (hzero : ∀ D : Set (ℝ × ℝ), areaIntegral (laplacian u) D = 0) :
    laplacian u p ≠ 0 → False := by
  intro hne
  obtain ⟨σ, hσ, r, hr, hpos⟩ := gap11 u p hcont hne
  rw [hzero (Metric.ball p r)] at hpos
  simp at hpos

theorem gap13
    (u : ℝ → ℝ → ℝ) (hcont : Continuous (laplacian u))
    (hzero : ∀ D : Set (ℝ × ℝ), areaIntegral (laplacian u) D = 0) :
    IsHarmonic u := by
  intro p
  by_contra hne
  exact gap12 u p hcont hzero hne

private lemma deriv_fst_section_eq_fderiv
    (f : ℝ × ℝ → ℝ) (hf : Differentiable ℝ f)
    (p : ℝ × ℝ) :
    deriv (fun x => f (x, p.2)) p.1 =
      fderiv ℝ f p (1, 0) := by
  have hfAt : HasFDerivAt f (fderiv ℝ f p) p :=
    (hf p).hasFDerivAt
  have hsection :
      HasFDerivAt (fun x : ℝ => (x, p.2))
        (ContinuousLinearMap.inl ℝ ℝ ℝ) p.1 :=
    hasFDerivAt_prodMk_left p.1 p.2
  have H :=
    hfAt.comp p.1 hsection
  simpa [Function.comp_def] using H.hasDerivAt.deriv

private lemma deriv_snd_section_eq_fderiv
    (f : ℝ × ℝ → ℝ) (hf : Differentiable ℝ f)
    (p : ℝ × ℝ) :
    deriv (fun y => f (p.1, y)) p.2 =
      fderiv ℝ f p (0, 1) := by
  have hfAt : HasFDerivAt f (fderiv ℝ f p) p :=
    (hf p).hasFDerivAt
  have hsection :
      HasFDerivAt (fun y : ℝ => (p.1, y))
        (ContinuousLinearMap.inr ℝ ℝ ℝ) p.2 :=
    hasFDerivAt_prodMk_right p.1 p.2
  have H :=
    hfAt.comp p.2 hsection
  simpa [Function.comp_def] using H.hasDerivAt.deriv

private lemma contDiff_partialX
    (u : ℝ → ℝ → ℝ) (hu : IsC2 u) :
    ContDiff ℝ 1 (partialX u) := by
  unfold IsC2 at hu
  have hdiff :
      Differentiable ℝ (fun p : ℝ × ℝ => u p.1 p.2) :=
    hu.differentiable two_ne_zero
  have heq :
      partialX u =
        fun p => fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2) p (1, 0) := by
    funext p
    exact deriv_fst_section_eq_fderiv _ hdiff p
  rw [heq]
  exact
    (hu.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const

private lemma contDiff_partialY
    (u : ℝ → ℝ → ℝ) (hu : IsC2 u) :
    ContDiff ℝ 1 (partialY u) := by
  unfold IsC2 at hu
  have hdiff :
      Differentiable ℝ (fun p : ℝ × ℝ => u p.1 p.2) :=
    hu.differentiable two_ne_zero
  have heq :
      partialY u =
        fun p => fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2) p (0, 1) := by
    funext p
    exact deriv_snd_section_eq_fderiv _ hdiff p
  rw [heq]
  exact
    (hu.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const

private lemma continuous_partialXX
    (u : ℝ → ℝ → ℝ) (hu : IsC2 u) :
    Continuous (partialXX u) := by
  have hx := contDiff_partialX u hu
  have hdiff : Differentiable ℝ (partialX u) :=
    hx.differentiable (by norm_num)
  have heq :
      partialXX u =
        fun p => fderiv ℝ (partialX u) p (1, 0) := by
    funext p
    exact deriv_fst_section_eq_fderiv _ hdiff p
  rw [heq]
  exact
    ((hx.fderiv_right (m := 0) (by norm_num)).clm_apply
      contDiff_const).continuous

private lemma continuous_partialYY
    (u : ℝ → ℝ → ℝ) (hu : IsC2 u) :
    Continuous (partialYY u) := by
  have hy := contDiff_partialY u hu
  have hdiff : Differentiable ℝ (partialY u) :=
    hy.differentiable (by norm_num)
  have heq :
      partialYY u =
        fun p => fderiv ℝ (partialY u) p (0, 1) := by
    funext p
    exact deriv_snd_section_eq_fderiv _ hdiff p
  rw [heq]
  exact
    ((hy.fderiv_right (m := 0) (by norm_num)).clm_apply
      contDiff_const).continuous

private lemma continuous_laplacian
    (u : ℝ → ℝ → ℝ) (hu : IsC2 u) :
    Continuous (laplacian u) := by
  unfold laplacian
  exact (continuous_partialXX u hu).add
    (continuous_partialYY u hu)

private def euclideanCenter (p : ℝ × ℝ) : ℂ :=
  Complex.equivRealProdCLM.symm p

private def euclideanDisk (p : ℝ × ℝ) (r : ℝ) :
    Set (ℝ × ℝ) :=
  Complex.equivRealProdCLM ''
    Metric.closedBall (euclideanCenter p) r

private def positiveCircle
    (p : ℝ × ℝ) (r t : ℝ) : ℝ × ℝ :=
  Complex.equivRealProdCLM
    (circleMap (euclideanCenter p) r (2 * Real.pi * t))

private lemma positiveCircle_apply
    (p : ℝ × ℝ) (r t : ℝ) :
    positiveCircle p r t =
      (p.1 + r * Real.cos (2 * Real.pi * t),
        p.2 + r * Real.sin (2 * Real.pi * t)) := by
  let θ : ℝ := 2 * Real.pi * t
  have hexp :
      Complex.exp ((θ : ℂ) * Complex.I) =
        (Real.cos θ : ℂ) +
          (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
  rw [positiveCircle]
  change
    Complex.equivRealProdCLM
        (euclideanCenter p + (r : ℂ) *
          Complex.exp ((θ : ℂ) * Complex.I)) = _
  rw [hexp]
  apply Prod.ext
  · simp only [Complex.equivRealProdCLM_apply,
      euclideanCenter, Complex.equivRealProdCLM_symm_apply,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    dsimp [θ]
    ring
  · simp only [Complex.equivRealProdCLM_apply,
      euclideanCenter, Complex.equivRealProdCLM_symm_apply,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    dsimp [θ]
    ring

private lemma deriv_positiveCircle_fst
    (p : ℝ × ℝ) (r t : ℝ) :
    deriv (fun s => (positiveCircle p r s).1) t =
      -(r * (2 * Real.pi) *
        Real.sin (2 * Real.pi * t)) := by
  have hfun :
      (fun s => (positiveCircle p r s).1) =
        fun s => p.1 + r * Real.cos (2 * Real.pi * s) := by
    funext s
    rw [positiveCircle_apply]
  rw [hfun]
  have hangle :
      HasDerivAt (fun s : ℝ => 2 * Real.pi * s)
        (2 * Real.pi) t := by
    convert
      (hasDerivAt_const t (2 * Real.pi)).mul
        (hasDerivAt_id t) using 1 <;> ring
  have H :=
    ((Real.hasDerivAt_cos (2 * Real.pi * t)).comp t
      hangle).const_mul r |>.const_add p.1
  convert H.deriv using 1 <;> ring

private lemma deriv_positiveCircle_snd
    (p : ℝ × ℝ) (r t : ℝ) :
    deriv (fun s => (positiveCircle p r s).2) t =
      r * (2 * Real.pi) *
        Real.cos (2 * Real.pi * t) := by
  have hfun :
      (fun s => (positiveCircle p r s).2) =
        fun s => p.2 + r * Real.sin (2 * Real.pi * s) := by
    funext s
    rw [positiveCircle_apply]
  rw [hfun]
  have hangle :
      HasDerivAt (fun s : ℝ => 2 * Real.pi * s)
        (2 * Real.pi) t := by
    convert
      (hasDerivAt_const t (2 * Real.pi)).mul
        (hasDerivAt_id t) using 1 <;> ring
  have H :=
    ((Real.hasDerivAt_sin (2 * Real.pi * t)).comp t
      hangle).const_mul r |>.const_add p.2
  convert H.deriv using 1 <;> ring

private lemma contDiff_positiveCircle
    (p : ℝ × ℝ) (r : ℝ) :
    ContDiff ℝ 1 (positiveCircle p r) := by
  have hangle :
      ContDiff ℝ 1 (fun t : ℝ => 2 * Real.pi * t) :=
    contDiff_const.mul contDiff_id
  have hcos :
      ContDiff ℝ 1
        (fun t : ℝ => Real.cos (2 * Real.pi * t)) :=
    by simpa only [Function.comp_apply] using
      Real.contDiff_cos.comp hangle
  have hsin :
      ContDiff ℝ 1
        (fun t : ℝ => Real.sin (2 * Real.pi * t)) :=
    by simpa only [Function.comp_apply] using
      Real.contDiff_sin.comp hangle
  have hpair :
      ContDiff ℝ 1
        (fun t : ℝ =>
          (p.1 + r * Real.cos (2 * Real.pi * t),
            p.2 + r * Real.sin (2 * Real.pi * t))) :=
    (contDiff_const.add (contDiff_const.mul hcos)).prodMk
      (contDiff_const.add (contDiff_const.mul hsin))
  convert hpair using 1
  funext t
  exact positiveCircle_apply p r t

private lemma positiveCircle_zero_eq_one
    (p : ℝ × ℝ) (r : ℝ) :
    positiveCircle p r 0 = positiveCircle p r 1 := by
  rw [positiveCircle_apply, positiveCircle_apply]
  simp

private lemma injOn_positiveCircle_Ico
    (p : ℝ × ℝ) (r : ℝ) (hr : 0 < r) :
    Set.InjOn (positiveCircle p r) (Set.Ico (0 : ℝ) 1) := by
  intro a ha b hb hab
  have hcircle :
      circleMap (euclideanCenter p) r (2 * Real.pi * a) =
        circleMap (euclideanCenter p) r
          (2 * Real.pi * b) := by
    apply Complex.equivRealProdCLM.injective
    exact hab
  have ha' :
      2 * Real.pi * a ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
    constructor
    · exact mul_nonneg Real.two_pi_pos.le ha.1
    · simpa only [mul_one] using
        mul_lt_mul_of_pos_left ha.2 Real.two_pi_pos
  have hb' :
      2 * Real.pi * b ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
    constructor
    · exact mul_nonneg Real.two_pi_pos.le hb.1
    · simpa only [mul_one] using
        mul_lt_mul_of_pos_left hb.2 Real.two_pi_pos
  have hangle :=
    injOn_circleMap_of_abs_sub_le' (c := euclideanCenter p)
      hr.ne' (by linarith [Real.pi_pos]) ha' hb' hcircle
  nlinarith [Real.pi_pos]

private lemma image_positiveCircle_Icc
    (p : ℝ × ℝ) (r : ℝ) (hr : 0 < r) :
    positiveCircle p r '' Set.Icc (0 : ℝ) 1 =
      frontier (euclideanDisk p r) := by
  let e : ℂ ≃ₜ ℝ × ℝ :=
    Complex.equivRealProdCLM.toHomeomorph
  have hfront :
      frontier (euclideanDisk p r) =
        e '' Metric.sphere (euclideanCenter p) r := by
    unfold euclideanDisk
    change
      frontier
          (e '' Metric.closedBall (euclideanCenter p) r) =
        e '' Metric.sphere (euclideanCenter p) r
    rw [← e.image_frontier,
      frontier_closedBall (euclideanCenter p) hr.ne']
  rw [hfront]
  apply Set.Subset.antisymm
  · rintro q ⟨t, ht, rfl⟩
    refine ⟨circleMap (euclideanCenter p) r
      (2 * Real.pi * t), ?_, rfl⟩
    exact circleMap_mem_sphere _ hr.le _
  · rintro q ⟨z, hz, rfl⟩
    have hz' :
        z ∈ circleMap (euclideanCenter p) r ''
          Set.Ioc (0 : ℝ) (2 * Real.pi) := by
      rw [image_circleMap_Ioc, abs_of_pos hr]
      exact hz
    obtain ⟨θ, hθ, rfl⟩ := hz'
    refine ⟨θ / (2 * Real.pi), ?_, ?_⟩
    · exact ⟨div_nonneg hθ.1.le Real.two_pi_pos.le,
        (div_le_one Real.two_pi_pos).2 hθ.2⟩
    · have hangle :
          2 * Real.pi * (θ / (2 * Real.pi)) = θ := by
        field_simp [Real.two_pi_pos.ne']
      change
        Complex.equivRealProdCLM
            (circleMap (euclideanCenter p) r
              (2 * Real.pi * (θ / (2 * Real.pi)))) =
          Complex.equivRealProdCLM
            (circleMap (euclideanCenter p) r θ)
      rw [hangle]

private lemma speed_positiveCircle
    (p : ℝ × ℝ) (r t : ℝ) (hr : 0 < r) :
    speed (positiveCircle p r) t =
      r * (2 * Real.pi) := by
  unfold speed tangent
  rw [deriv_positiveCircle_fst,
    deriv_positiveCircle_snd]
  have htrig :=
    Real.sin_sq_add_cos_sq (2 * Real.pi * t)
  have hsquares :
      (-(r * (2 * Real.pi) *
          Real.sin (2 * Real.pi * t))) ^ 2 +
          (r * (2 * Real.pi) *
            Real.cos (2 * Real.pi * t)) ^ 2 =
        (r * (2 * Real.pi)) ^ 2 := by
    nlinarith
  rw [hsquares, Real.sqrt_sq_eq_abs,
    abs_of_pos (mul_pos hr Real.two_pi_pos)]

private lemma bounded_euclideanDisk
    (p : ℝ × ℝ) (r : ℝ) :
    Bornology.IsBounded (euclideanDisk p r) := by
  unfold euclideanDisk
  change
    Bornology.IsBounded
      (Complex.equivRealProd ''
        Metric.closedBall (euclideanCenter p) r)
  exact Complex.lipschitz_equivRealProd.isBounded_image
    Metric.isBounded_closedBall

private lemma euclideanDisk_eq_closure_interior
    (p : ℝ × ℝ) (r : ℝ) (hr : 0 < r) :
    euclideanDisk p r =
      closure (interior (euclideanDisk p r)) := by
  let e : ℂ ≃ₜ ℝ × ℝ :=
    Complex.equivRealProdCLM.toHomeomorph
  unfold euclideanDisk
  change
    e '' Metric.closedBall (euclideanCenter p) r =
      closure
        (interior
          (e '' Metric.closedBall (euclideanCenter p) r))
  rw [← e.image_interior,
    interior_closedBall (euclideanCenter p) hr.ne',
    ← e.image_closure,
    closure_ball (euclideanCenter p) hr.ne']

private lemma orientation_integral_positive
    (p : ℝ × ℝ) (r : ℝ) (hr : 0 < r) :
    0 < ∫ t in (0 : ℝ)..1,
      (positiveCircle p r t).1 *
          deriv (fun s => (positiveCircle p r s).2) t -
        (positiveCircle p r t).2 *
          deriv (fun s => (positiveCircle p r s).1) t := by
  let g : ℝ → ℝ := fun t =>
    (p.1 + r * Real.cos (2 * Real.pi * t)) *
        (r * (2 * Real.pi) *
          Real.cos (2 * Real.pi * t)) -
      (p.2 + r * Real.sin (2 * Real.pi * t)) *
        (-(r * (2 * Real.pi) *
          Real.sin (2 * Real.pi * t)))
  have hintegral :
      (∫ t in (0 : ℝ)..1,
        (positiveCircle p r t).1 *
            deriv (fun s => (positiveCircle p r s).2) t -
          (positiveCircle p r t).2 *
            deriv (fun s => (positiveCircle p r s).1) t) =
        ∫ t in (0 : ℝ)..1, g t := by
    apply intervalIntegral.integral_congr
    intro t ht
    change
      (positiveCircle p r t).1 *
            deriv (fun s => (positiveCircle p r s).2) t -
          (positiveCircle p r t).2 *
            deriv (fun s => (positiveCircle p r s).1) t =
        g t
    rw [positiveCircle_apply,
      deriv_positiveCircle_fst,
      deriv_positiveCircle_snd]
  rw [hintegral]
  let F : ℝ → ℝ := fun t =>
    p.1 * r * Real.sin (2 * Real.pi * t) -
      p.2 * r * Real.cos (2 * Real.pi * t) +
      r ^ 2 * (2 * Real.pi) * t
  have hFderiv : ∀ t : ℝ, HasDerivAt F (g t) t := by
    intro t
    have hangle :
        HasDerivAt (fun s : ℝ => 2 * Real.pi * s)
          (2 * Real.pi) t := by
      convert
        (hasDerivAt_const t (2 * Real.pi)).mul
          (hasDerivAt_id t) using 1 <;> ring
    have hsin :=
      (Real.hasDerivAt_sin (2 * Real.pi * t)).comp t
        hangle
    have hcos :=
      (Real.hasDerivAt_cos (2 * Real.pi * t)).comp t
        hangle
    have H :=
      ((hsin.const_mul (p.1 * r)).sub
        (hcos.const_mul (p.2 * r))).add
          ((hasDerivAt_id t).const_mul
            (r ^ 2 * (2 * Real.pi)))
    convert H using 1
    dsimp [g]
    have htrig :=
      Real.sin_sq_add_cos_sq (2 * Real.pi * t)
    calc
      _ = 2 * Real.pi *
          (p.1 * r * Real.cos (2 * Real.pi * t) +
            p.2 * r * Real.sin (2 * Real.pi * t) +
            r ^ 2 *
              (Real.sin (2 * Real.pi * t) ^ 2 +
                Real.cos (2 * Real.pi * t) ^ 2)) := by ring
      _ = _ := by rw [htrig]; ring
  have hangle_cont :
      Continuous (fun t : ℝ => 2 * Real.pi * t) :=
    continuous_const.mul continuous_id
  have hcos_cont :
      Continuous
        (fun t : ℝ => Real.cos (2 * Real.pi * t)) :=
    Real.continuous_cos.comp hangle_cont
  have hsin_cont :
      Continuous
        (fun t : ℝ => Real.sin (2 * Real.pi * t)) :=
    Real.continuous_sin.comp hangle_cont
  have hgcont : Continuous g := by
    dsimp [g]
    exact
      (continuous_const.add
          (continuous_const.mul hcos_cont)).mul
        (continuous_const.mul hcos_cont) |>.sub
      ((continuous_const.add
          (continuous_const.mul hsin_cont)).mul
        (continuous_const.mul hsin_cont).neg)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := 1) (fun t ht => hFderiv t)
      (hgcont.intervalIntegrable 0 1)]
  dsimp [F]
  simp
  nlinarith [mul_pos hr Real.two_pi_pos]

private lemma isPositiveBoundary_positiveCircle
    (p : ℝ × ℝ) (r : ℝ) (hr : 0 < r) :
    IsPositiveBoundary (positiveCircle p r)
      (euclideanDisk p r) := by
  refine ⟨contDiff_positiveCircle p r,
    positiveCircle_zero_eq_one p r,
    injOn_positiveCircle_Ico p r hr,
    image_positiveCircle_Icc p r hr, ?_,
    bounded_euclideanDisk p r,
    euclideanDisk_eq_closure_interior p r hr,
    orientation_integral_positive p r hr⟩
  intro t ht
  rw [speed_positiveCircle p r t hr]
  exact mul_pos hr Real.two_pi_pos

private lemma euclideanDisk_subset_ball
    (p : ℝ × ℝ) (R r : ℝ) (hRr : R < r) :
    euclideanDisk p R ⊆ Metric.ball p r := by
  rintro q ⟨z, hz, rfl⟩
  have hcenter :
      Complex.equivRealProdCLM (euclideanCenter p) = p := by
    simp [euclideanCenter]
  have hlip :=
    Complex.lipschitz_equivRealProd.dist_le_mul z
      (euclideanCenter p)
  have hdist :
      dist
          (Complex.equivRealProdCLM z)
          (Complex.equivRealProdCLM (euclideanCenter p)) ≤
        dist z (euclideanCenter p) := by
    simpa [Complex.equivRealProdCLM_apply] using hlip
  rw [Metric.mem_ball, ← hcenter]
  exact lt_of_le_of_lt hdist
    (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hRr)

private lemma center_mem_interior_euclideanDisk
    (p : ℝ × ℝ) (r : ℝ) (hr : 0 < r) :
    p ∈ interior (euclideanDisk p r) := by
  let e : ℂ ≃ₜ ℝ × ℝ :=
    Complex.equivRealProdCLM.toHomeomorph
  unfold euclideanDisk
  change
    p ∈ interior
      (e '' Metric.closedBall (euclideanCenter p) r)
  rw [← e.image_interior,
    interior_closedBall (euclideanCenter p) hr.ne']
  refine ⟨euclideanCenter p, Metric.mem_ball_self hr, ?_⟩
  simp [e, euclideanCenter]

private lemma compact_euclideanDisk
    (p : ℝ × ℝ) (r : ℝ) :
    IsCompact (euclideanDisk p r) := by
  unfold euclideanDisk
  have hclosed :
      IsCompact
        (Metric.closedBall (euclideanCenter p) r) :=
    isCompact_closedBall (euclideanCenter p) r
  exact hclosed.image
    Complex.equivRealProdCLM.continuous

private lemma positive_signed_area_euclideanDisk
    (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (r σ : ℝ)
    (hcont : Continuous (laplacian u)) (hr : 0 < r)
    (hpos : ∀ q ∈ euclideanDisk p r,
      0 < σ * laplacian u q) :
    0 < σ *
      areaIntegral (laplacian u) (euclideanDisk p r) := by
  let f : ℝ × ℝ → ℝ := fun q => σ * laplacian u q
  have hfcont : Continuous f := continuous_const.mul hcont
  have hcompact := compact_euclideanDisk p r
  have hmeas : MeasurableSet (euclideanDisk p r) :=
    hcompact.measurableSet
  have hfint : IntegrableOn f (euclideanDisk p r) :=
    hfcont.continuousOn.integrableOn_compact hcompact
  have hnonneg :
      0 ≤ᵐ[volume.restrict (euclideanDisk p r)] f :=
    ae_restrict_of_forall_mem hmeas
      (fun q hq => (hpos q hq).le)
  have hsupp :
      euclideanDisk p r ⊆ Function.support f := by
    intro q hq
    exact Function.mem_support.mpr (ne_of_gt (hpos q hq))
  have hmeasure :
      0 < volume (euclideanDisk p r) :=
    Measure.measure_pos_of_nonempty_interior volume
      ⟨p, center_mem_interior_euclideanDisk p r hr⟩
  unfold areaIntegral
  rw [← MeasureTheory.integral_const_mul]
  apply
    (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hfint).2
  rw [Set.inter_eq_right.mpr hsupp]
  exact hmeasure

theorem gap14
    (u : ℝ → ℝ → ℝ) (hu : IsC2 u)
    (hGreen : GreenTheoremForPositiveBoundaries) :
    IsHarmonic u ↔
      ∀ (γ : ℝ → ℝ × ℝ) (D : Set (ℝ × ℝ)),
        IsPositiveBoundary γ D → normalFlux u γ = 0 := by
  constructor
  · intro hharm γ D hboundary
    have hregular :
        ∀ t ∈ Set.Icc (0 : ℝ) 1, speed γ t ≠ 0 :=
      fun t ht => ne_of_gt (hboundary.2.2.2.2.1 t ht)
    calc
      normalFlux u γ = wedgeFlux u γ :=
        gap4 u γ hregular
      _ = areaIntegral (laplacian u) D :=
        hGreen γ D hboundary u hu
      _ = 0 := gap9 u hharm D
  · intro hzeroFlux
    intro p
    by_contra hne
    have hcont : Continuous (laplacian u) :=
      continuous_laplacian u hu
    obtain ⟨σ, hσ, r, hr, hpos⟩ :=
      gap10 u p hcont hne
    let R : ℝ := r / 2
    have hR : 0 < R := by
      dsimp [R]
      linarith
    have hRr : R < r := by
      dsimp [R]
      linarith
    have hsubset :
        euclideanDisk p R ⊆ Metric.ball p r :=
      euclideanDisk_subset_ball p R r hRr
    have hposDisk :
        ∀ q ∈ euclideanDisk p R,
          0 < σ * laplacian u q :=
      fun q hq => hpos q (hsubset hq)
    have hpositive :
        0 < σ *
          areaIntegral (laplacian u)
            (euclideanDisk p R) :=
      positive_signed_area_euclideanDisk
        u p R σ hcont hR hposDisk
    have hboundary :
        IsPositiveBoundary (positiveCircle p R)
          (euclideanDisk p R) :=
      isPositiveBoundary_positiveCircle p R hR
    have hflux :
        normalFlux u (positiveCircle p R) = 0 :=
      hzeroFlux (positiveCircle p R)
        (euclideanDisk p R) hboundary
    have hfluxArea :
        normalFlux u (positiveCircle p R) =
          areaIntegral (laplacian u)
            (euclideanDisk p R) :=
      gap7 u (positiveCircle p R)
        (euclideanDisk p R) hu hboundary
          (hGreen (positiveCircle p R)
            (euclideanDisk p R) hboundary)
    rw [hfluxArea] at hflux
    rw [hflux] at hpositive
    simp at hpositive

end

end ProofGap.Exercise4331
