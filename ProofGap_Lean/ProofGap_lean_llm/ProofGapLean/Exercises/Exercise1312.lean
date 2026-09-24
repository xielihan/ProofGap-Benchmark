import ProofGapLean.Prelude.Analysis
import ProofGapLean.Exercises.Exercise1266
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1312

noncomputable section

def segmentPoint (x₁ x₂ t : ℝ) : ℝ :=
  (1 - t) * x₁ + t * x₂

def chord (f : ℝ → ℝ) (x₁ x₂ t : ℝ) : ℝ :=
  (1 - t) * f x₁ + t * f x₂

def chordGap (f : ℝ → ℝ) (x₁ x₂ t : ℝ) : ℝ :=
  f (segmentPoint x₁ x₂ t) - chord f x₁ x₂ t

def SecondOrderOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  a < b ∧ ContDiffOn ℝ 2 f (Set.Ioo a b)

def PositiveSecondOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Set.Ioo a b, 0 < deriv (deriv f) x

def NegativeSecondOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Set.Ioo a b, deriv (deriv f) x < 0

def ValidWeights (w₁ w₂ : ℝ) : Prop :=
  0 < w₁ ∧ 0 < w₂ ∧ w₁ + w₂ = 1

theorem gap1 (f : ℝ → ℝ) (a b : ℝ)
    (h : ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b,
      x₁ ≠ x₂ → ∀ w₁ w₂, ValidWeights w₁ w₂ →
        f (w₁ * x₁ + w₂ * x₂) <
          w₁ * f x₁ + w₂ * f x₂) :
    StrictConvexOn ℝ (Set.Ioo a b) f := by
  refine ⟨convex_Ioo a b, ?_⟩
  intro x₁ hx₁ x₂ hx₂ h12 w₁ w₂ hw₁ hw₂ hsum
  simpa only [smul_eq_mul] using
    h x₁ hx₁ x₂ hx₂ h12 w₁ w₂ ⟨hw₁, hw₂, hsum⟩

theorem gap2 (f : ℝ → ℝ) (a b : ℝ)
    (h : ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b,
      x₁ ≠ x₂ → ∀ w₁ w₂, ValidWeights w₁ w₂ →
        w₁ * f x₁ + w₂ * f x₂ <
          f (w₁ * x₁ + w₂ * x₂)) :
    StrictConcaveOn ℝ (Set.Ioo a b) f := by
  refine ⟨convex_Ioo a b, ?_⟩
  intro x₁ hx₁ x₂ hx₂ h12 w₁ w₂ hw₁ hw₂ hsum
  simpa only [smul_eq_mul] using
    h x₁ hx₁ x₂ hx₂ h12 w₁ w₂ ⟨hw₁, hw₂, hsum⟩

theorem gap3 (f : ℝ → ℝ) (x₁ x₂ : ℝ) :
    chordGap f x₁ x₂ 0 = f x₁ - f x₁ := by
  simp [chordGap, segmentPoint, chord]

theorem gap4 (f : ℝ → ℝ) (x₁ : ℝ) :
    f x₁ - f x₁ = 0 := by
  ring

theorem gap5 (f : ℝ → ℝ) (x₁ x₂ : ℝ) :
    chordGap f x₁ x₂ 0 = 0 := by
  rw [gap3, gap4]

theorem gap6 (f : ℝ → ℝ) (x₁ x₂ : ℝ) :
    chordGap f x₁ x₂ 1 = f x₂ - f x₂ := by
  simp [chordGap, segmentPoint, chord]

theorem gap7 (f : ℝ → ℝ) (x₂ : ℝ) :
    f x₂ - f x₂ = 0 := by
  ring

theorem gap8 (f : ℝ → ℝ) (x₁ x₂ : ℝ) :
    chordGap f x₁ x₂ 1 = 0 := by
  rw [gap6, gap7]

theorem gap9 (f : ℝ → ℝ) (x₁ x₂ t : ℝ)
    (hf : DifferentiableAt ℝ f (segmentPoint x₁ x₂ t)) :
    deriv (chordGap f x₁ x₂) t =
      (x₂ - x₁) * deriv f (segmentPoint x₁ x₂ t) -
        (f x₂ - f x₁) := by
  have hseg : HasDerivAt (segmentPoint x₁ x₂) (x₂ - x₁) t := by
    have hcalc :=
      (((hasDerivAt_const (x := t) (1 : ℝ)).sub (hasDerivAt_id t)).mul_const x₁).add
        ((hasDerivAt_id t).mul_const x₂)
    convert hcalc using 1
    · ring
  have hchord : HasDerivAt (chord f x₁ x₂) (f x₂ - f x₁) t := by
    have hcalc :=
      (((hasDerivAt_const (x := t) (1 : ℝ)).sub (hasDerivAt_id t)).mul_const
        (f x₁)).add ((hasDerivAt_id t).mul_const (f x₂))
    convert hcalc using 1
    · ring
  convert (hf.hasDerivAt.comp t hseg).sub hchord |>.deriv using 1 <;>
    simp [chordGap] <;> ring

theorem gap10 (f : ℝ → ℝ) (a b x₁ x₂ : ℝ)
    (hreg : SecondOrderOn f a b)
    (hx₁ : x₁ ∈ Set.Ioo a b) (hx₂ : x₂ ∈ Set.Ioo a b)
    (h12 : x₁ < x₂) :
    ∃ c ∈ Set.Ioo x₁ x₂,
      f x₂ - f x₁ = (x₂ - x₁) * deriv f c := by
  have hsub : Set.Icc x₁ x₂ ⊆ Set.Ioo a b := by
    intro x hx
    exact ⟨hx₁.1.trans_le hx.1, hx.2.trans_lt hx₂.2⟩
  have hdiff : DifferentiableOn ℝ f (Set.Icc x₁ x₂) :=
    (hreg.2.differentiableOn (by decide)).mono hsub
  obtain ⟨c, hc, heq⟩ :=
    exists_deriv_eq_slope f h12 hdiff.continuousOn
      (hdiff.mono Set.Ioo_subset_Icc_self)
  refine ⟨c, hc, ?_⟩
  rw [heq]
  field_simp [sub_ne_zero.mpr h12.ne']

theorem gap11 (f : ℝ → ℝ) (x₁ x₂ t c : ℝ)
    (hf : DifferentiableAt ℝ f (segmentPoint x₁ x₂ t))
    (hc : f x₂ - f x₁ = (x₂ - x₁) * deriv f c) :
    deriv (chordGap f x₁ x₂) t =
      (x₂ - x₁) *
        (deriv f (segmentPoint x₁ x₂ t) - deriv f c) := by
  rw [gap9 f x₁ x₂ t hf, hc]
  ring

theorem gap12 (x₁ x₂ c : ℝ) (hc : c ∈ Set.Ioo x₁ x₂) :
    x₁ < c := by
  exact hc.1

theorem gap13 (x₁ x₂ c : ℝ) (hc : c ∈ Set.Ioo x₁ x₂) :
    c < x₂ := by
  exact hc.2

theorem gap14 (x₁ x₂ : ℝ) (h : x₁ < x₂) : x₁ < x₂ := by
  exact h

def parameterOf (x₁ x₂ c : ℝ) : ℝ :=
  (c - x₁) / (x₂ - x₁)

theorem gap15 (x₁ x₂ c : ℝ) (hc : c ∈ Set.Ioo x₁ x₂) :
    0 < parameterOf x₁ x₂ c := by
  exact div_pos (sub_pos.mpr hc.1) (sub_pos.mpr (hc.1.trans hc.2))

theorem gap16 (x₁ x₂ c : ℝ) (hc : c ∈ Set.Ioo x₁ x₂) :
    parameterOf x₁ x₂ c < 1 := by
  rw [parameterOf, div_lt_one (sub_pos.mpr (hc.1.trans hc.2))]
  linarith [hc.2]

theorem gap17 (x₁ x₂ c : ℝ) (hc : c ∈ Set.Ioo x₁ x₂) :
    c = segmentPoint x₁ x₂ (parameterOf x₁ x₂ c) := by
  unfold segmentPoint parameterOf
  field_simp [sub_ne_zero.mpr (hc.1.trans hc.2).ne']
  ring

theorem gap18 (f : ℝ → ℝ) (a b x₁ x₂ c : ℝ)
    (hreg : SecondOrderOn f a b)
    (hx₁ : x₁ ∈ Set.Ioo a b) (hx₂ : x₂ ∈ Set.Ioo a b)
    (hc : c ∈ Set.Ioo x₁ x₂)
    (hmvt : f x₂ - f x₁ = (x₂ - x₁) * deriv f c) :
    deriv (chordGap f x₁ x₂) (parameterOf x₁ x₂ c) = 0 := by
  have hc_ab : c ∈ Set.Ioo a b :=
    ⟨hx₁.1.trans hc.1, hc.2.trans hx₂.2⟩
  have hfc : DifferentiableAt ℝ f c :=
    (hreg.2.differentiableOn (by decide) c hc_ab).differentiableAt
      (Ioo_mem_nhds hc_ab.1 hc_ab.2)
  have hcparam := gap17 x₁ x₂ c hc
  have hfparam : DifferentiableAt ℝ f
      (segmentPoint x₁ x₂ (parameterOf x₁ x₂ c)) := by
    rwa [← hcparam]
  rw [gap11 f x₁ x₂ (parameterOf x₁ x₂ c) c hfparam hmvt, ← hcparam]
  ring

theorem gap19 (f : ℝ → ℝ) (x₁ x₂ t : ℝ)
    (hf : ContDiffAt ℝ 2 f (segmentPoint x₁ x₂ t)) :
    deriv (deriv (chordGap f x₁ x₂)) t =
      (x₂ - x₁) ^ 2 *
        deriv (deriv f) (segmentPoint x₁ x₂ t) := by
  have hseg : HasDerivAt (segmentPoint x₁ x₂) (x₂ - x₁) t := by
    have hcalc :=
      (((hasDerivAt_const (x := t) (1 : ℝ)).sub (hasDerivAt_id t)).mul_const x₁).add
        ((hasDerivAt_id t).mul_const x₂)
    convert hcalc using 1
    · ring
  have hnear : ∀ᶠ s in nhds t,
      ContDiffAt ℝ 2 f (segmentPoint x₁ x₂ s) :=
    hseg.continuousAt (hf.eventually (by decide))
  have heq : deriv (chordGap f x₁ x₂) =ᶠ[nhds t]
      fun s ↦ (x₂ - x₁) * deriv f (segmentPoint x₁ x₂ s) -
        (f x₂ - f x₁) := by
    filter_upwards [hnear] with s hs
    exact gap9 f x₁ x₂ s (hs.differentiableAt (by decide))
  have hdf : DifferentiableAt ℝ (deriv f) (segmentPoint x₁ x₂ t) :=
    (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hexplicit : HasDerivAt
      (fun s ↦ (x₂ - x₁) * deriv f (segmentPoint x₁ x₂ s) -
        (f x₂ - f x₁))
      ((x₂ - x₁) ^ 2 * deriv (deriv f) (segmentPoint x₁ x₂ t)) t := by
    convert ((hdf.hasDerivAt.comp t hseg).const_mul (x₂ - x₁)).sub_const
      (f x₂ - f x₁) using 1 <;> ring
  calc
    deriv (deriv (chordGap f x₁ x₂)) t =
        deriv (fun s ↦ (x₂ - x₁) * deriv f (segmentPoint x₁ x₂ s) -
          (f x₂ - f x₁)) t := heq.deriv_eq
    _ = (x₂ - x₁) ^ 2 *
        deriv (deriv f) (segmentPoint x₁ x₂ t) := hexplicit.deriv

private theorem segmentPoint_mem_Ioo
    (a b x₁ x₂ t : ℝ)
    (hx₁ : x₁ ∈ Set.Ioo a b) (hx₂ : x₂ ∈ Set.Ioo a b)
    (h12 : x₁ < x₂) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    segmentPoint x₁ x₂ t ∈ Set.Ioo a b := by
  have hprod₀ : 0 ≤ t * (x₂ - x₁) :=
    mul_nonneg ht.1 (sub_nonneg.mpr h12.le)
  have hprod₁ : 0 ≤ (1 - t) * (x₂ - x₁) :=
    mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr h12.le)
  have hform₀ :
      segmentPoint x₁ x₂ t = x₁ + t * (x₂ - x₁) := by
    unfold segmentPoint
    ring
  have hform₁ :
      segmentPoint x₁ x₂ t = x₂ - (1 - t) * (x₂ - x₁) := by
    unfold segmentPoint
    ring
  constructor
  · rw [hform₀]
    nlinarith [hx₁.1, hprod₀]
  · rw [hform₁]
    nlinarith [hx₂.2, hprod₁]

theorem gap20 (f : ℝ → ℝ) (a b x₁ x₂ t : ℝ)
    (hreg : SecondOrderOn f a b)
    (hpos : PositiveSecondOn f a b)
    (hx₁ : x₁ ∈ Set.Ioo a b) (hx₂ : x₂ ∈ Set.Ioo a b)
    (h12 : x₁ < x₂) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < deriv (deriv (chordGap f x₁ x₂)) t := by
  have hpoint := segmentPoint_mem_Ioo a b x₁ x₂ t hx₁ hx₂ h12 ht
  have hf2 : ContDiffAt ℝ 2 f (segmentPoint x₁ x₂ t) :=
    (hreg.2 _ hpoint).contDiffAt (Ioo_mem_nhds hpoint.1 hpoint.2)
  rw [gap19 f x₁ x₂ t hf2]
  exact mul_pos (sq_pos_of_pos (sub_pos.mpr h12)) (hpos _ hpoint)

theorem gap21 (f : ℝ → ℝ) (a b x₁ x₂ : ℝ)
    (hreg : SecondOrderOn f a b)
    (hpos : PositiveSecondOn f a b)
    (hx₁ : x₁ ∈ Set.Ioo a b) (hx₂ : x₂ ∈ Set.Ioo a b)
    (h12 : x₁ < x₂) :
    StrictMonoOn (deriv (chordGap f x₁ x₂)) (Set.Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
  · intro t ht
    exact (differentiableAt_of_deriv_ne_zero
      (gap20 f a b x₁ x₂ t hreg hpos hx₁ hx₂ h12 ht).ne').continuousAt.continuousWithinAt
  · intro t ht
    exact gap20 f a b x₁ x₂ t hreg hpos hx₁ hx₂ h12 (interior_subset ht)

theorem gap22 (f : ℝ → ℝ) (x₁ x₂ t t₀ : ℝ)
    (hmono : StrictMonoOn (deriv (chordGap f x₁ x₂)) (Set.Icc 0 1))
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1)
    (hlt : t < t₀) (hzero : deriv (chordGap f x₁ x₂) t₀ = 0) :
    deriv (chordGap f x₁ x₂) t < 0 := by
  rw [← hzero]
  exact hmono ht ht₀ hlt

theorem gap23 (f : ℝ → ℝ) (x₁ x₂ t t₀ : ℝ)
    (hmono : StrictMonoOn (deriv (chordGap f x₁ x₂)) (Set.Icc 0 1))
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1)
    (hlt : t₀ < t) (hzero : deriv (chordGap f x₁ x₂) t₀ = 0) :
    0 < deriv (chordGap f x₁ x₂) t := by
  rw [← hzero]
  exact hmono ht₀ ht hlt

theorem gap24 (f : ℝ → ℝ) (x₁ x₂ t₀ : ℝ)
    (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn (chordGap f x₁ x₂) (Set.Icc 0 t₀))
    (hleft : ∀ t ∈ Set.Ico (0 : ℝ) t₀,
      deriv (chordGap f x₁ x₂) t < 0) :
    StrictAntiOn (chordGap f x₁ x₂) (Set.Icc 0 t₀) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 t₀) hcont
  intro t ht
  apply hleft t
  have ht' : t ∈ Set.Ioo (0 : ℝ) t₀ := by
    simpa only [interior_Icc] using ht
  exact ⟨ht'.1.le, ht'.2⟩

theorem gap25 (f : ℝ → ℝ) (x₁ x₂ t₀ : ℝ)
    (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn (chordGap f x₁ x₂) (Set.Icc t₀ 1))
    (hright : ∀ t ∈ Set.Ioc t₀ 1,
      0 < deriv (chordGap f x₁ x₂) t) :
    StrictMonoOn (chordGap f x₁ x₂) (Set.Icc t₀ 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc t₀ 1) hcont
  intro t ht
  apply hright t
  have ht' : t ∈ Set.Ioo t₀ (1 : ℝ) := by
    simpa only [interior_Icc] using ht
  exact ⟨ht'.1, ht'.2.le⟩

theorem gap26 (f : ℝ → ℝ) (a b x₁ x₂ t : ℝ)
    (hreg : SecondOrderOn f a b)
    (hpos : PositiveSecondOn f a b)
    (hx₁ : x₁ ∈ Set.Ioo a b) (hx₂ : x₂ ∈ Set.Ioo a b)
    (h12 : x₁ < x₂) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    chordGap f x₁ x₂ t < 0 := by
  have hconv : StrictConvexOn ℝ (Set.Ioo a b) f := by
    apply strictConvexOn_of_deriv2_pos' (convex_Ioo a b) hreg.2.continuousOn
    intro x hx
    simpa [Function.iterate_succ_apply] using hpos x hx
  have hlt := hconv.2 hx₁ hx₂ h12.ne (sub_pos.mpr ht.2) ht.1
    (by linarith : (1 - t) + t = 1)
  simpa [chordGap, segmentPoint, chord, smul_eq_mul] using sub_neg.mpr hlt

theorem gap27 (f : ℝ → ℝ) (a b x₁ x₂ w₂ : ℝ)
    (hreg : SecondOrderOn f a b)
    (hpos : PositiveSecondOn f a b)
    (hx₁ : x₁ ∈ Set.Ioo a b) (hx₂ : x₂ ∈ Set.Ioo a b)
    (h12 : x₁ < x₂) (hw : w₂ ∈ Set.Ioo (0 : ℝ) 1) :
    chordGap f x₁ x₂ w₂ < 0 := by
  exact gap26 f a b x₁ x₂ w₂ hreg hpos hx₁ hx₂ h12 hw

theorem gap28 (f : ℝ → ℝ) (a b x₁ x₂ w₁ w₂ : ℝ)
    (hreg : SecondOrderOn f a b)
    (hpos : PositiveSecondOn f a b)
    (hx₁ : x₁ ∈ Set.Ioo a b) (hx₂ : x₂ ∈ Set.Ioo a b)
    (h12 : x₁ < x₂) (hw : ValidWeights w₁ w₂) :
    f (w₁ * x₁ + w₂ * x₂) <
      w₁ * f x₁ + w₂ * f x₂ := by
  have hconv : StrictConvexOn ℝ (Set.Ioo a b) f := by
    apply strictConvexOn_of_deriv2_pos' (convex_Ioo a b) hreg.2.continuousOn
    intro x hx
    simpa [Function.iterate_succ_apply] using hpos x hx
  simpa only [smul_eq_mul] using
    hconv.2 hx₁ hx₂ h12.ne hw.1 hw.2.1 hw.2.2

theorem gap29 (f : ℝ → ℝ) (a b : ℝ)
    (hreg : SecondOrderOn f a b)
    (hpos : PositiveSecondOn f a b) :
    StrictConvexOn ℝ (Set.Ioo a b) f := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioo a b) hreg.2.continuousOn
  intro x hx
  simpa [Function.iterate_succ_apply] using hpos x hx

theorem gap30 (f : ℝ → ℝ) (a b x₁ x₂ t : ℝ)
    (hreg : SecondOrderOn f a b)
    (hneg : NegativeSecondOn f a b)
    (hx₁ : x₁ ∈ Set.Ioo a b) (hx₂ : x₂ ∈ Set.Ioo a b)
    (h12 : x₁ < x₂) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    deriv (deriv (chordGap f x₁ x₂)) t < 0 := by
  have hpoint := segmentPoint_mem_Ioo a b x₁ x₂ t hx₁ hx₂ h12 ht
  have hf2 : ContDiffAt ℝ 2 f (segmentPoint x₁ x₂ t) :=
    (hreg.2 _ hpoint).contDiffAt (Ioo_mem_nhds hpoint.1 hpoint.2)
  rw [gap19 f x₁ x₂ t hf2]
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos (sub_pos.mpr h12)) (hneg _ hpoint)

theorem gap31 (f : ℝ → ℝ) (a b x₁ x₂ t : ℝ)
    (hreg : SecondOrderOn f a b)
    (hneg : NegativeSecondOn f a b)
    (hx₁ : x₁ ∈ Set.Ioo a b) (hx₂ : x₂ ∈ Set.Ioo a b)
    (h12 : x₁ < x₂) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    0 < chordGap f x₁ x₂ t := by
  have hconc : StrictConcaveOn ℝ (Set.Ioo a b) f := by
    apply strictConcaveOn_of_deriv2_neg' (convex_Ioo a b) hreg.2.continuousOn
    intro x hx
    simpa [Function.iterate_succ_apply] using hneg x hx
  have hlt := hconc.2 hx₁ hx₂ h12.ne (sub_pos.mpr ht.2) ht.1
    (by linarith : (1 - t) + t = 1)
  simpa [chordGap, segmentPoint, chord, smul_eq_mul] using sub_pos.mpr hlt

theorem gap32 (f : ℝ → ℝ) (a b x₁ x₂ w₂ : ℝ)
    (hreg : SecondOrderOn f a b)
    (hneg : NegativeSecondOn f a b)
    (hx₁ : x₁ ∈ Set.Ioo a b) (hx₂ : x₂ ∈ Set.Ioo a b)
    (h12 : x₁ < x₂) (hw : w₂ ∈ Set.Ioo (0 : ℝ) 1) :
    0 < chordGap f x₁ x₂ w₂ := by
  exact gap31 f a b x₁ x₂ w₂ hreg hneg hx₁ hx₂ h12 hw

theorem gap33 (f : ℝ → ℝ) (a b x₁ x₂ w₁ w₂ : ℝ)
    (hreg : SecondOrderOn f a b)
    (hneg : NegativeSecondOn f a b)
    (hx₁ : x₁ ∈ Set.Ioo a b) (hx₂ : x₂ ∈ Set.Ioo a b)
    (h12 : x₁ < x₂) (hw : ValidWeights w₁ w₂) :
    w₁ * f x₁ + w₂ * f x₂ <
      f (w₁ * x₁ + w₂ * x₂) := by
  have hconc : StrictConcaveOn ℝ (Set.Ioo a b) f := by
    apply strictConcaveOn_of_deriv2_neg' (convex_Ioo a b) hreg.2.continuousOn
    intro x hx
    simpa [Function.iterate_succ_apply] using hneg x hx
  simpa only [smul_eq_mul] using
    hconc.2 hx₁ hx₂ h12.ne hw.1 hw.2.1 hw.2.2

theorem gap34 (f : ℝ → ℝ) (a b : ℝ)
    (hreg : SecondOrderOn f a b)
    (hneg : NegativeSecondOn f a b) :
    StrictConcaveOn ℝ (Set.Ioo a b) f := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioo a b) hreg.2.continuousOn
  intro x hx
  simpa [Function.iterate_succ_apply] using hneg x hx

theorem gap35 (x₁ x₂ w₁ w₂ : ℝ) (h12 : x₁ < x₂)
    (hw : ValidWeights w₁ w₂) :
    x₁ < w₁ * x₁ + w₂ * x₂ := by
  have hp : 0 < w₂ * (x₂ - x₁) :=
    mul_pos hw.2.1 (sub_pos.mpr h12)
  have hw₁ : w₁ = 1 - w₂ := by linarith [hw.2.2]
  rw [hw₁]
  nlinarith

theorem gap36 (x₁ x₂ w₁ w₂ : ℝ) (h12 : x₁ < x₂)
    (hw : ValidWeights w₁ w₂) :
    w₁ * x₁ + w₂ * x₂ < x₂ := by
  have hp : 0 < w₁ * (x₂ - x₁) :=
    mul_pos hw.1 (sub_pos.mpr h12)
  have hw₂ : w₂ = 1 - w₁ := by linarith [hw.2.2]
  rw [hw₂]
  nlinarith

theorem gap37 (x₁ x₂ : ℝ) (h12 : x₁ < x₂) : x₁ < x₂ := by
  exact h12

theorem gap38 (f : ℝ → ℝ) (a b x t : ℝ)
    (hreg : SecondOrderOn f a b)
    (hx : x ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b)
    (hxt : x ≠ t) :
    ∃ ξ ∈ Set.Ioo (min x t) (max x t),
      f x = f t + (x - t) * deriv f t +
        (1 / 2 : ℝ) * (x - t) ^ 2 * deriv (deriv f) ξ := by
  have hxtorder : min x t < max x t := by
    rcases lt_or_gt_of_ne hxt with h | h <;> simp [h]
  have hsub : Set.Icc (min x t) (max x t) ⊆ Set.Ioo a b := by
    intro y hy
    constructor
    · exact (lt_min hx.1 ht.1).trans_le hy.1
    · exact hy.2.trans_lt (max_lt hx.2 ht.2)
  have hfd : DifferentiableOn ℝ f (Set.Icc (min x t) (max x t)) :=
    (hreg.2.differentiableOn (by decide)).mono hsub
  have hfd' : DifferentiableOn ℝ (deriv f) (Set.Icc (min x t) (max x t)) := by
    intro y hy
    have hyab := hsub hy
    have hfy : ContDiffAt ℝ 2 f y :=
      (hreg.2 y hyab).contDiffAt (Ioo_mem_nhds hyab.1 hyab.2)
    exact ((hfy.derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).differentiableWithinAt
  simpa [ProofGap.Exercise1266.secondDeriv, mul_comm] using
    ProofGap.Exercise1266.gap1 f (min x t) (max x t) x t hxtorder
      (by simp) (by simp) hxt hfd hfd'

theorem gap39 (f : ℝ → ℝ) (a b x₁ x₂ w₁ w₂ : ℝ)
    (hreg : SecondOrderOn f a b)
    (hx₁ : x₁ ∈ Set.Ioo a b) (hx₂ : x₂ ∈ Set.Ioo a b)
    (h12 : x₁ < x₂) (hw : ValidWeights w₁ w₂) :
    ∃ ξ₁ ∈ Set.Ioo (min x₁ (w₁ * x₁ + w₂ * x₂))
        (max x₁ (w₁ * x₁ + w₂ * x₂)),
      f x₁ = f (w₁ * x₁ + w₂ * x₂) +
        (x₁ - (w₁ * x₁ + w₂ * x₂)) *
          deriv f (w₁ * x₁ + w₂ * x₂) +
        (1 / 2 : ℝ) *
          (x₁ - (w₁ * x₁ + w₂ * x₂)) ^ 2 *
          deriv (deriv f) ξ₁ := by
  have hmleft := gap35 x₁ x₂ w₁ w₂ h12 hw
  have hmright := gap36 x₁ x₂ w₁ w₂ h12 hw
  have hm : w₁ * x₁ + w₂ * x₂ ∈ Set.Ioo a b :=
    ⟨hx₁.1.trans hmleft, hmright.trans hx₂.2⟩
  exact gap38 f a b x₁ (w₁ * x₁ + w₂ * x₂) hreg hx₁ hm hmleft.ne

theorem gap40 (f : ℝ → ℝ) (a b x₁ x₂ w₁ w₂ : ℝ)
    (hreg : SecondOrderOn f a b)
    (hx₁ : x₁ ∈ Set.Ioo a b) (hx₂ : x₂ ∈ Set.Ioo a b)
    (h12 : x₁ < x₂) (hw : ValidWeights w₁ w₂) :
    ∃ ξ₂ ∈ Set.Ioo (min x₂ (w₁ * x₁ + w₂ * x₂))
        (max x₂ (w₁ * x₁ + w₂ * x₂)),
      f x₂ = f (w₁ * x₁ + w₂ * x₂) +
        (x₂ - (w₁ * x₁ + w₂ * x₂)) *
          deriv f (w₁ * x₁ + w₂ * x₂) +
        (1 / 2 : ℝ) *
          (x₂ - (w₁ * x₁ + w₂ * x₂)) ^ 2 *
          deriv (deriv f) ξ₂ := by
  have hmleft := gap35 x₁ x₂ w₁ w₂ h12 hw
  have hmright := gap36 x₁ x₂ w₁ w₂ h12 hw
  have hm : w₁ * x₁ + w₂ * x₂ ∈ Set.Ioo a b :=
    ⟨hx₁.1.trans hmleft, hmright.trans hx₂.2⟩
  exact gap38 f a b x₂ (w₁ * x₁ + w₂ * x₂) hreg hx₂ hm hmright.ne'

theorem gap41 (f : ℝ → ℝ) (x₁ x₂ w₁ w₂ ξ₁ ξ₂ : ℝ)
    (hw : ValidWeights w₁ w₂)
    (hTaylor1 :
      f x₁ = f (w₁ * x₁ + w₂ * x₂) +
        (x₁ - (w₁ * x₁ + w₂ * x₂)) *
          deriv f (w₁ * x₁ + w₂ * x₂) +
        (1 / 2 : ℝ) * (x₁ - (w₁ * x₁ + w₂ * x₂)) ^ 2 *
          deriv (deriv f) ξ₁)
    (hTaylor2 :
      f x₂ = f (w₁ * x₁ + w₂ * x₂) +
        (x₂ - (w₁ * x₁ + w₂ * x₂)) *
          deriv f (w₁ * x₁ + w₂ * x₂) +
        (1 / 2 : ℝ) * (x₂ - (w₁ * x₁ + w₂ * x₂)) ^ 2 *
          deriv (deriv f) ξ₂) :
    w₁ * f x₁ + w₂ * f x₂ -
        f (w₁ * x₁ + w₂ * x₂) =
      (1 / 2 : ℝ) *
        (w₁ * (x₁ - (w₁ * x₁ + w₂ * x₂)) ^ 2 *
            deriv (deriv f) ξ₁ +
          w₂ * (x₂ - (w₁ * x₁ + w₂ * x₂)) ^ 2 *
            deriv (deriv f) ξ₂) := by
  rw [hTaylor1, hTaylor2]
  rcases hw with ⟨hw₁, hw₂, hsum⟩
  have hw₂eq : w₂ = 1 - w₁ := by linarith
  rw [hw₂eq]
  ring

theorem gap42 (f : ℝ → ℝ) (a b x₁ x₂ w₁ w₂ : ℝ)
    (hreg : SecondOrderOn f a b)
    (hpos : PositiveSecondOn f a b)
    (hx₁ : x₁ ∈ Set.Ioo a b) (hx₂ : x₂ ∈ Set.Ioo a b)
    (h12 : x₁ < x₂) (hw : ValidWeights w₁ w₂) :
    f (w₁ * x₁ + w₂ * x₂) <
      w₁ * f x₁ + w₂ * f x₂ := by
  exact gap28 f a b x₁ x₂ w₁ w₂ hreg hpos hx₁ hx₂ h12 hw

theorem gap43 (f : ℝ → ℝ) (a b : ℝ)
    (hreg : SecondOrderOn f a b)
    (hpos : PositiveSecondOn f a b) :
    StrictConvexOn ℝ (Set.Ioo a b) f := by
  exact gap29 f a b hreg hpos

theorem gap44 (f : ℝ → ℝ) (a b x₁ x₂ w₁ w₂ : ℝ)
    (hreg : SecondOrderOn f a b)
    (hneg : NegativeSecondOn f a b)
    (hx₁ : x₁ ∈ Set.Ioo a b) (hx₂ : x₂ ∈ Set.Ioo a b)
    (h12 : x₁ < x₂) (hw : ValidWeights w₁ w₂) :
    w₁ * f x₁ + w₂ * f x₂ <
      f (w₁ * x₁ + w₂ * x₂) := by
  exact gap33 f a b x₁ x₂ w₁ w₂ hreg hneg hx₁ hx₂ h12 hw

theorem gap45 (f : ℝ → ℝ) (a b : ℝ)
    (hreg : SecondOrderOn f a b)
    (hneg : NegativeSecondOn f a b) :
    StrictConcaveOn ℝ (Set.Ioo a b) f := by
  exact gap34 f a b hreg hneg

theorem gap46 (f : ℝ → ℝ) (a b : ℝ)
    (hreg : SecondOrderOn f a b) :
    (PositiveSecondOn f a b →
      StrictConvexOn ℝ (Set.Ioo a b) f) ∧
    (NegativeSecondOn f a b →
      StrictConcaveOn ℝ (Set.Ioo a b) f) := by
  exact ⟨gap43 f a b hreg, gap45 f a b hreg⟩

end

end ProofGap.Exercise1312
