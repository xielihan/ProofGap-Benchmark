import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.TietzeExtension
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4186

noncomputable section

open Filter MeasureTheory Set
open scoped Interval

def rectangle (a A b B : ℝ) : Set (ℝ × ℝ) :=
  {z | a ≤ z.1 ∧ z.1 ≤ A ∧ b ≤ z.2 ∧ z.2 ≤ B}

def modelKernel (f : ℝ → ℝ) (p x y : ℝ) : ℝ :=
  1 / Real.rpow |f x - y| p

def weightedKernel (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (p x y : ℝ) : ℝ :=
  phi (x, y) / Real.rpow |f x - y| p

def parameterIntegral (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (p b B x : ℝ) : ℝ :=
  ∫ y in b..B, weightedKernel phi f p x y

def shiftedKernel (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (p x t : ℝ) : ℝ :=
  phi (x, t + f x) / Real.rpow |t| p

def shiftedLower (f : ℝ → ℝ) (b x : ℝ) : ℝ :=
  b - f x

def shiftedUpper (f : ℝ → ℝ) (B x : ℝ) : ℝ :=
  B - f x

def differenceTermOne (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (p b B x₁ x₂ : ℝ) : ℝ :=
  ∫ t in shiftedLower f b x₁..shiftedUpper f B x₁,
    shiftedKernel phi f p x₁ t - shiftedKernel phi f p x₂ t

def differenceTermTwo (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (p b x₁ x₂ : ℝ) : ℝ :=
  ∫ t in shiftedLower f b x₂..shiftedLower f b x₁,
    shiftedKernel phi f p x₂ t

def differenceTermThree (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (p B x₁ x₂ : ℝ) : ℝ :=
  ∫ t in shiftedUpper f B x₂..shiftedUpper f B x₁,
    shiftedKernel phi f p x₂ t

private theorem rectangle_eq_prod (a A b B : ℝ) :
    rectangle a A b B = Set.Icc a A ×ˢ Set.Icc b B := by
  ext z
  simp only [rectangle, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc]
  aesop

private theorem rectangle_compact (a A b B : ℝ) :
    IsCompact (rectangle a A b B) := by
  rw [rectangle_eq_prod]
  exact isCompact_Icc.prod isCompact_Icc

private def singularKernel (p t : ℝ) : ℝ :=
  1 / Real.rpow |t| p

private theorem singularKernel_eq (p t : ℝ) :
    singularKernel p t = Real.rpow |t| (-p) := by
  unfold singularKernel
  rw [one_div]
  exact (Real.rpow_neg (abs_nonneg t) p).symm

private theorem singularKernel_nonneg (p t : ℝ) :
    0 ≤ singularKernel p t := by
  rw [singularKernel_eq]
  exact Real.rpow_nonneg (abs_nonneg t) (-p)

private theorem singularKernel_measurable (p : ℝ) :
    Measurable (singularKernel p) := by
  have heq :
      singularKernel p = (fun t : ℝ => Real.rpow |t| (-p)) := by
    funext t
    exact singularKernel_eq p t
  rw [heq]
  apply measurable_of_continuousOn_compl_singleton (0 : ℝ)
  apply continuousOn_of_forall_continuousAt
  intro t ht
  simpa [Function.comp_def] using
    (Real.continuousAt_rpow_const |t| (-p)
      (Or.inl (abs_ne_zero.mpr ht))).comp continuous_abs.continuousAt

private theorem singularKernel_intervalIntegrable
    (p c d : ℝ) (hp : p < 1) :
    IntervalIntegrable (singularKernel p) volume c d := by
  let R : ℝ := max |c| |d| + 1
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hs : -1 < -p := by linarith
  have hbase :
      IntervalIntegrable (fun t : ℝ => Real.rpow t (-p))
        volume 0 R :=
    intervalIntegral.intervalIntegrable_rpow' hs
  have hpos :
      IntervalIntegrable (singularKernel p) volume 0 R := by
    apply hbase.congr
    intro t ht
    have ht' : t ∈ Set.Ioc 0 R := by
      simpa [Set.uIoc_of_le hR.le] using ht
    rw [singularKernel_eq, abs_of_nonneg ht'.1.le]
  have hnegBase :
      IntervalIntegrable (fun t : ℝ => Real.rpow (-t) (-p))
        volume (-R) 0 := by
    have h :=
      (IntervalIntegrable.iff_comp_neg
        (f := fun t : ℝ => Real.rpow t (-p))).mp hbase
    simpa using h.symm
  have hneg :
      IntervalIntegrable (singularKernel p) volume (-R) 0 := by
    apply hnegBase.congr
    intro t ht
    have ht' : t ∈ Set.Ioc (-R) 0 := by
      simpa [Set.uIoc_of_le (neg_nonpos.mpr hR.le)] using ht
    rw [singularKernel_eq, abs_of_nonpos ht'.2]
  have hfull :
      IntervalIntegrable (singularKernel p) volume (-R) R :=
    hneg.trans hpos
  apply hfull.mono_set'
  intro t ht
  have hcR : |c| < R := by
    dsimp [R]
    linarith [le_max_left |c| |d|]
  have hdR : |d| < R := by
    dsimp [R]
    linarith [le_max_right |c| |d|]
  have hcL : -R < c := (neg_lt_neg hcR).trans_le (neg_abs_le c)
  have hdL : -R < d := (neg_lt_neg hdR).trans_le (neg_abs_le d)
  have hcU : c < R := (le_abs_self c).trans_lt hcR
  have hdU : d < R := (le_abs_self d).trans_lt hdR
  rw [Set.uIoc_of_le (neg_le_self hR.le)]
  rw [Set.mem_uIoc] at ht
  rcases ht with ⟨hct, htd⟩ | ⟨hdt, htc⟩
  · exact ⟨hcL.trans hct, htd.trans hdU.le⟩
  · exact ⟨hdL.trans hdt, htc.trans hcU.le⟩

private theorem modelKernel_eq_singular
    (f : ℝ → ℝ) (p x y : ℝ) :
    modelKernel f p x y = singularKernel p (f x - y) := by
  rfl

private theorem shiftedKernel_eq_mul
    (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ) (p x t : ℝ) :
    shiftedKernel phi f p x t =
      phi (x, t + f x) * singularKernel p t := by
  simp [shiftedKernel, singularKernel, div_eq_mul_inv]

theorem gap1 (f : ℝ → ℝ) (a A b B p x : ℝ)
    (hp : p < 1) (hx : x ∈ Set.Icc a A) :
    IntervalIntegrable (fun y => modelKernel f p x y) volume b B := by
  have h :=
    (singularKernel_intervalIntegrable
      p (f x - B) (f x - b) hp).comp_sub_left (f x)
  simpa [modelKernel_eq_singular] using h.symm

theorem gap2 (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (a A b B p x : ℝ)
    (haA : a ≤ A) (hbB : b ≤ B) (hp : p < 1)
    (hx : x ∈ Set.Icc a A)
    (hphi : ContinuousOn phi (rectangle a A b B)) :
    IntervalIntegrable
      (fun y => weightedKernel phi f p x y) volume b B := by
  have hsec : ContinuousOn (fun y : ℝ => phi (x, y)) (Set.Icc b B) := by
    apply hphi.comp (continuous_const.prodMk continuous_id).continuousOn
    intro y hy
    exact ⟨hx.1, hx.2, hy.1, hy.2⟩
  have hk := gap1 f a A b B p x hp hx
  have hsec' :
      ContinuousOn (fun y : ℝ => phi (x, y)) (Set.uIcc b B) := by
    simpa [Set.uIcc_of_le hbB] using hsec
  have hmul := hk.continuousOn_mul hsec'
  simpa [weightedKernel, modelKernel, singularKernel, div_eq_mul_inv] using hmul

theorem gap3 (phi : ℝ × ℝ → ℝ) (a A b B : ℝ)
    (hphi : ContinuousOn phi (rectangle a A b B)) :
    ContinuousOn phi (rectangle a A b B) := by
  exact hphi

theorem gap4 (phi : ℝ × ℝ → ℝ) (a A b B : ℝ)
    (haA : a ≤ A) (hbB : b ≤ B)
    (hphi : ContinuousOn phi (rectangle a A b B)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ rectangle a A b B, |phi z| ≤ M := by
  have hb :
      BddAbove ((fun z : ℝ × ℝ => |phi z|) ''
        rectangle a A b B) :=
    (rectangle_compact a A b B).bddAbove_image hphi.abs
  rcases hb with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz
  exact (hC ⟨z, hz, rfl⟩).trans (le_max_left _ _)

theorem gap5 (f : ℝ → ℝ) (a A b B p : ℝ)
    (haA : a ≤ A) (hbB : b ≤ B) (hp : p < 1)
    (hf : ContinuousOn f (Set.Icc a A)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ Set.Icc a A, ∀ y ∈ Set.Icc b B,
        Real.rpow |f x - y| (1 - p) ≤ M := by
  let S : Set (ℝ × ℝ) := Set.Icc a A ×ˢ Set.Icc b B
  have hfS : ContinuousOn (fun z : ℝ × ℝ => f z.1) S := by
    apply hf.comp continuous_fst.continuousOn
    intro z hz
    exact hz.1
  have harg :
      ContinuousOn (fun z : ℝ × ℝ => |f z.1 - z.2|) S :=
    (hfS.sub continuous_snd.continuousOn).abs
  have hexp : 0 ≤ 1 - p := by linarith
  have hpow :
      ContinuousOn
        (fun z : ℝ × ℝ => Real.rpow |f z.1 - z.2| (1 - p)) S := by
    exact (Real.continuous_rpow_const hexp).continuousOn.comp
      harg (fun _ _ => Set.mem_univ _)
  rcases (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      hpow with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx y hy
  have h := hC (x, y) ⟨hx, hy⟩
  have h' : Real.rpow |f x - y| (1 - p) ≤ C := by
    let v : ℝ := Real.rpow |f x - y| (1 - p)
    change ‖v‖ ≤ C at h
    have hv : 0 ≤ v := by
      dsimp [v]
      exact Real.rpow_nonneg (abs_nonneg (f x - y)) (1 - p)
    rw [Real.norm_of_nonneg hv] at h
    simpa [v] using h
  exact h'.trans (le_max_left _ _)

theorem gap6 (phi : ℝ × ℝ → ℝ) (a A b B : ℝ)
    (haA : a ≤ A) (hbB : b ≤ B)
    (hphi : ContinuousOn phi (rectangle a A b B)) :
    ∀ epsilon > 0, ∃ delta > 0,
      ∀ z₁ ∈ rectangle a A b B, ∀ z₂ ∈ rectangle a A b B,
        |z₁.1 - z₂.1| < delta →
        |z₁.2 - z₂.2| < delta →
        |phi z₁ - phi z₂| < epsilon := by
  have hu :=
    (rectangle_compact a A b B).uniformContinuousOn_of_continuous hphi
  rw [Metric.uniformContinuousOn_iff] at hu
  intro epsilon hepsilon
  rcases hu epsilon hepsilon with ⟨delta, hdelta, hδ⟩
  refine ⟨delta, hdelta, ?_⟩
  intro z₁ hz₁ z₂ hz₂ h1 h2
  have hdist : dist z₁ z₂ < delta := by
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    exact ⟨h1, h2⟩
  simpa [Real.dist_eq] using hδ z₁ hz₁ z₂ hz₂ hdist

theorem gap7 (f : ℝ → ℝ) (a A : ℝ)
    (haA : a ≤ A) (hf : ContinuousOn f (Set.Icc a A)) :
    ∀ epsilon > 0, ∃ delta > 0,
      ∀ x₁ ∈ Set.Icc a A, ∀ x₂ ∈ Set.Icc a A,
        |x₁ - x₂| < delta →
        |f x₁ - f x₂| < epsilon := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at hu
  intro epsilon hepsilon
  rcases hu epsilon hepsilon with ⟨delta, hdelta, hδ⟩
  refine ⟨delta, hdelta, ?_⟩
  intro x₁ hx₁ x₂ hx₂ h
  simpa [Real.dist_eq] using hδ x₁ hx₁ x₂ hx₂ (by simpa [Real.dist_eq] using h)

theorem gap8 (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (a A b B y : ℝ)
    (haA : a ≤ A) (hbB : b ≤ B)
    (hphi : ContinuousOn phi (rectangle a A b B))
    (hf : ContinuousOn f (Set.Icc a A)) :
    ∀ epsilon > 0, ∃ delta > 0,
      ∀ x₁ ∈ Set.Icc a A, ∀ x₂ ∈ Set.Icc a A,
        (x₁, y + f x₁) ∈ rectangle a A b B →
        (x₂, y + f x₂) ∈ rectangle a A b B →
        |x₁ - x₂| < delta →
        |phi (x₁, y + f x₁) - phi (x₂, y + f x₂)| <
          epsilon := by
  intro epsilon hepsilon
  rcases gap6 phi a A b B haA hbB hphi epsilon hepsilon with
    ⟨d, hd, hφd⟩
  rcases gap7 f a A haA hf d hd with ⟨e, he, hfe⟩
  refine ⟨min d e, lt_min hd he, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hz₁ hz₂ hx
  apply hφd (x₁, y + f x₁) hz₁ (x₂, y + f x₂) hz₂
  · exact hx.trans_le (min_le_left _ _)
  · simpa only [add_sub_add_left_eq_sub] using
      hfe x₁ hx₁ x₂ hx₂ (hx.trans_le (min_le_right _ _))

private theorem parameterIntegral_eq_shifted
    (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ) (p b B x : ℝ) :
    parameterIntegral phi f p b B x =
      ∫ t in shiftedLower f b x..shiftedUpper f B x,
        shiftedKernel phi f p x t := by
  have h :=
    intervalIntegral.integral_comp_add_right
      (fun y : ℝ => weightedKernel phi f p x y) (f x)
      (a := b - f x) (b := B - f x)
  rw [show b - f x + f x = b by ring,
    show B - f x + f x = B by ring] at h
  rw [parameterIntegral, ← h]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [weightedKernel, shiftedKernel]
  congr 2
  rw [show f x - (t + f x) = -t by ring, abs_neg]

theorem gap9 (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (p b B x₁ x₂ : ℝ)
    (h₁ : Integrable (shiftedKernel phi f p x₁))
    (h₂ : Integrable (shiftedKernel phi f p x₂)) :
    parameterIntegral phi f p b B x₁ -
        parameterIntegral phi f p b B x₂ =
      differenceTermOne phi f p b B x₁ x₂ -
        differenceTermTwo phi f p b x₁ x₂ +
        differenceTermThree phi f p B x₁ x₂ := by
  rw [parameterIntegral_eq_shifted, parameterIntegral_eq_shifted]
  unfold differenceTermOne differenceTermTwo differenceTermThree
  rw [intervalIntegral.integral_sub h₁.intervalIntegrable h₂.intervalIntegrable]
  have hlo :=
    intervalIntegral.integral_add_adjacent_intervals
      (f := shiftedKernel phi f p x₂)
      (a := shiftedLower f b x₂)
      (b := shiftedLower f b x₁)
      (c := shiftedUpper f B x₁)
      h₂.intervalIntegrable h₂.intervalIntegrable
  have hup :=
    intervalIntegral.integral_add_adjacent_intervals
      (f := shiftedKernel phi f p x₂)
      (a := shiftedLower f b x₂)
      (b := shiftedUpper f B x₂)
      (c := shiftedUpper f B x₁)
      h₂.intervalIntegrable h₂.intervalIntegrable
  linarith

private theorem exists_shifted_numerator_bound
    (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (a A c d : ℝ) (hphi : Continuous phi)
    (hf : ContinuousOn f (Set.Icc a A)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ Set.Icc a A, ∀ t ∈ Set.uIcc c d,
        |phi (x, t + f x)| ≤ M := by
  let S : Set (ℝ × ℝ) := Set.Icc a A ×ˢ Set.uIcc c d
  have hfS : ContinuousOn (fun z : ℝ × ℝ => f z.1) S := by
    apply hf.comp continuous_fst.continuousOn
    intro z hz
    exact hz.1
  have hmap :
      ContinuousOn
        (fun z : ℝ × ℝ => (z.1, z.2 + f z.1)) S :=
    continuous_fst.continuousOn.prodMk
      (continuous_snd.continuousOn.add hfS)
  have hcomp :
      ContinuousOn
        (fun z : ℝ × ℝ => phi (z.1, z.2 + f z.1)) S := by
    exact hphi.continuousOn.comp hmap (fun _ _ => Set.mem_univ _)
  rcases (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn
      hcomp with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx t ht
  have h := hC (x, t) ⟨hx, ht⟩
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

private theorem shiftedKernel_aestronglyMeasurable
    (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ) (p x : ℝ)
    (hphi : Continuous phi) :
    AEStronglyMeasurable (shiftedKernel phi f p x) volume := by
  have hnum : Continuous (fun t : ℝ => phi (x, t + f x)) := by
    exact hphi.comp
      (continuous_const.prodMk (continuous_id.add continuous_const))
  rw [show shiftedKernel phi f p x =
      fun t => phi (x, t + f x) * singularKernel p t by
        funext t
        exact shiftedKernel_eq_mul phi f p x t]
  exact (hnum.measurable.mul
    (singularKernel_measurable p)).aestronglyMeasurable

private theorem shiftedKernel_continuous_subtype
    (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (a A p t : ℝ) (hphi : Continuous phi)
    (hf : ContinuousOn f (Set.Icc a A)) :
    Continuous
      (fun x : ↥(Set.Icc a A) => shiftedKernel phi f p x t) := by
  have hfsub : Continuous (fun x : ↥(Set.Icc a A) => f x) :=
    (continuousOn_iff_continuous_restrict).mp hf
  have hnum :
      Continuous
        (fun x : ↥(Set.Icc a A) => phi (x, t + f x)) := by
    exact hphi.comp
      (continuous_subtype_val.prodMk
        (continuous_const.add hfsub))
  have hmul :
      Continuous
        (fun x : ↥(Set.Icc a A) =>
          phi (x, t + f x) * singularKernel p t) :=
    hnum.mul continuous_const
  apply hmul.congr
  intro x
  exact (shiftedKernel_eq_mul phi f p x t).symm

private theorem shiftedKernel_norm_bound
    (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (p M x t : ℝ)
    (hM : |phi (x, t + f x)| ≤ M) :
    ‖shiftedKernel phi f p x t‖ ≤ M * singularKernel p t := by
  rw [shiftedKernel_eq_mul, norm_mul, Real.norm_eq_abs,
    Real.norm_of_nonneg (singularKernel_nonneg p t)]
  exact mul_le_mul_of_nonneg_right hM (singularKernel_nonneg p t)

theorem gap10 (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (a A b B p x : ℝ)
    (haA : a ≤ A) (hbB : b ≤ B) (hp : p < 1)
    (hphi : Continuous phi)
    (hf : ContinuousOn f (Set.Icc a A))
    (hx : x ∈ Set.Icc a A) :
    Tendsto (fun x₂ => differenceTermOne phi f p b B x x₂)
      (nhdsWithin x (Set.Icc a A)) (nhds 0) := by
  let l := shiftedLower f b x
  let u := shiftedUpper f B x
  rcases exists_shifted_numerator_bound phi f a A l u hphi hf with
    ⟨M, hM0, hM⟩
  let F : ↥(Set.Icc a A) → ℝ → ℝ :=
    fun x₂ t =>
      shiftedKernel phi f p x t - shiftedKernel phi f p x₂ t
  let xS : ↥(Set.Icc a A) := ⟨x, hx⟩
  have hmeas :
      ∀ᶠ x₂ in nhds xS,
        AEStronglyMeasurable (F x₂) (volume.restrict (Ι l u)) := by
    filter_upwards with x₂
    exact
      ((shiftedKernel_aestronglyMeasurable phi f p x hphi).sub
        (shiftedKernel_aestronglyMeasurable phi f p x₂ hphi)).mono_measure
          Measure.restrict_le_self
  have hbound :
      ∀ᶠ x₂ in nhds xS, ∀ᵐ t ∂volume,
        t ∈ Ι l u → ‖F x₂ t‖ ≤ 2 * M * singularKernel p t := by
    filter_upwards with x₂
    filter_upwards with t
    intro ht
    have ht' : t ∈ Set.uIcc l u := Set.uIoc_subset_uIcc ht
    have h1 :=
      shiftedKernel_norm_bound phi f p M x t (hM x hx t ht')
    have h2 :=
      shiftedKernel_norm_bound phi f p M x₂ t (hM x₂ x₂.property t ht')
    calc
      ‖F x₂ t‖ ≤ ‖shiftedKernel phi f p x t‖ +
          ‖shiftedKernel phi f p x₂ t‖ := norm_sub_le _ _
      _ ≤ M * singularKernel p t + M * singularKernel p t :=
        add_le_add h1 h2
      _ = 2 * M * singularKernel p t := by ring
  have hboundInt :
      IntervalIntegrable (fun t => 2 * M * singularKernel p t)
        volume l u := by
    exact (singularKernel_intervalIntegrable p l u hp).const_mul (2 * M)
  have hcont :
      ∀ᵐ t ∂volume, t ∈ Ι l u →
        ContinuousAt (fun x₂ => F x₂ t) xS := by
    filter_upwards with t
    intro ht
    exact continuousAt_const.sub
      (shiftedKernel_continuous_subtype
        phi f a A p t hphi hf).continuousAt
  have hc :
      ContinuousAt
        (fun x₂ : ↥(Set.Icc a A) => ∫ t in l..u, F x₂ t) xS :=
    intervalIntegral.continuousAt_of_dominated_interval
      hmeas hbound hboundInt hcont
  have hc' :
      ContinuousWithinAt
        (fun x₂ => differenceTermOne phi f p b B x x₂)
        (Set.Icc a A) x := by
    apply (continuousWithinAt_iff_continuousAt_restrict _ hx).mpr
    simpa [differenceTermOne, F, l, u, xS] using hc
  have hz : differenceTermOne phi f p b B x x = 0 := by
    simp [differenceTermOne]
  have ht := hc'.tendsto
  rw [hz] at ht
  exact ht

private theorem shiftedKernel_moving_endpoint_tendsto
    (phi : ℝ × ℝ → ℝ) (f endpoint : ℝ → ℝ)
    (a A p x : ℝ)
    (hp : p < 1) (hphi : Continuous phi)
    (hf : ContinuousOn f (Set.Icc a A))
    (hendpoint : ContinuousOn endpoint (Set.Icc a A))
    (hx : x ∈ Set.Icc a A) :
    Tendsto
      (fun x₂ =>
        ∫ t in endpoint x₂..endpoint x,
          shiftedKernel phi f p x₂ t)
      (nhdsWithin x (Set.Icc a A)) (nhds 0) := by
  let e0 := endpoint x
  let c := e0 - 1
  let d := e0 + 1
  rcases exists_shifted_numerator_bound phi f a A c d hphi hf with
    ⟨M, hM0, hM⟩
  let S := ↥(Set.Icc a A)
  let xS : S := ⟨x, hx⟩
  let F : S → ℝ → ℝ :=
    fun x₂ t => shiftedKernel phi f p x₂ t
  have hFmeas :
      ∀ x₂, AEStronglyMeasurable (F x₂)
        (volume.restrict (Ι c d)) := by
    intro x₂
    exact
      (shiftedKernel_aestronglyMeasurable
        phi f p x₂ hphi).mono_measure Measure.restrict_le_self
  have hbound :
      ∀ᶠ x₂ in nhds xS,
        ∀ᵐ t ∂volume.restrict (Ι c d),
          ‖F x₂ t‖ ≤ M * singularKernel p t := by
    filter_upwards with x₂
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with t
    intro ht
    exact shiftedKernel_norm_bound phi f p M x₂ t
      (hM x₂ x₂.property t (Set.uIoc_subset_uIcc ht))
  have hboundInt :
      IntervalIntegrable (fun t => M * singularKernel p t)
        volume c d :=
    (singularKernel_intervalIntegrable p c d hp).const_mul M
  have hFcont :
      ∀ᵐ t ∂volume.restrict (Ι c d),
        ContinuousAt (fun x₂ => F x₂ t) xS := by
    filter_upwards with t
    exact
      (shiftedKernel_continuous_subtype
        phi f a A p t hphi hf).continuousAt
  have he0 : e0 ∈ Set.Ioo c d := by
    dsimp [c, d]
    constructor <;> linarith
  have hc :
      ContinuousAt
        (fun q : S × ℝ =>
          ∫ t in e0..q.2, F q.1 t) (xS, e0) :=
    intervalIntegral.continuousAt_parametric_primitive_of_dominated
      (fun t => M * singularKernel p t) c d
      (a₀ := e0) (b₀ := e0) (x₀ := xS)
      hFmeas hbound hboundInt hFcont he0 he0
      (measure_singleton e0)
  have hendpointSub : Continuous (fun z : S => endpoint z) :=
    (continuousOn_iff_continuous_restrict).mp hendpoint
  have hpair :
      Tendsto (fun z : S => (z, endpoint z))
        (nhds xS) (nhds (xS, e0)) := by
    exact continuousAt_id.prodMk hendpointSub.continuousAt
  have hforward :
      Tendsto
        (fun z : S => ∫ t in e0..endpoint z, F z t)
        (nhds xS) (nhds 0) := by
    have h := hc.tendsto.comp hpair
    simpa [e0, xS, F] using h
  have hbackward :
      Tendsto
        (fun z : S => ∫ t in endpoint z..e0, F z t)
        (nhds xS) (nhds 0) := by
    have hneg := hforward.neg
    convert hneg using 1
    · funext z
      rw [intervalIntegral.integral_symm]
    · norm_num
  apply (tendsto_nhdsWithin_iff_subtype hx
    (fun x₂ =>
      ∫ t in endpoint x₂..endpoint x,
        shiftedKernel phi f p x₂ t) (nhds 0)).mpr
  simpa [S, xS, F, e0] using hbackward

theorem gap11 (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (a A b B p x : ℝ)
    (haA : a ≤ A) (hbB : b ≤ B) (hp : p < 1)
    (hphi : Continuous phi)
    (hf : ContinuousOn f (Set.Icc a A))
    (hx : x ∈ Set.Icc a A) :
    Tendsto (fun x₂ => differenceTermTwo phi f p b x x₂)
      (nhdsWithin x (Set.Icc a A)) (nhds 0) := by
  have hend :
      ContinuousOn (shiftedLower f b) (Set.Icc a A) := by
    exact continuousOn_const.sub hf
  simpa [differenceTermTwo] using
    shiftedKernel_moving_endpoint_tendsto
      phi f (shiftedLower f b) a A p x hp hphi hf hend hx

theorem gap12 (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (a A b B p x : ℝ)
    (haA : a ≤ A) (hbB : b ≤ B) (hp : p < 1)
    (hphi : Continuous phi)
    (hf : ContinuousOn f (Set.Icc a A))
    (hx : x ∈ Set.Icc a A) :
    Tendsto (fun x₂ => differenceTermThree phi f p B x x₂)
      (nhdsWithin x (Set.Icc a A)) (nhds 0) := by
  have hend :
      ContinuousOn (shiftedUpper f B) (Set.Icc a A) := by
    exact continuousOn_const.sub hf
  simpa [differenceTermThree] using
    shiftedKernel_moving_endpoint_tendsto
      phi f (shiftedUpper f B) a A p x hp hphi hf hend hx

private theorem shiftedKernel_intervalIntegrable_of_continuous
    (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (p x c d : ℝ) (hp : p < 1) (hphi : Continuous phi) :
    IntervalIntegrable (shiftedKernel phi f p x) volume c d := by
  have hnum :
      ContinuousOn (fun t : ℝ => phi (x, t + f x)) (Set.uIcc c d) := by
    exact
      (hphi.comp
        (continuous_const.prodMk
          (continuous_id.add continuous_const))).continuousOn
  have h :=
    (singularKernel_intervalIntegrable p c d hp).continuousOn_mul hnum
  apply h.congr
  intro t ht
  exact (shiftedKernel_eq_mul phi f p x t).symm

private theorem parameter_difference_identity
    (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (p b B x₁ x₂ : ℝ) (hp : p < 1)
    (hphi : Continuous phi) :
    parameterIntegral phi f p b B x₁ -
        parameterIntegral phi f p b B x₂ =
      differenceTermOne phi f p b B x₁ x₂ -
        differenceTermTwo phi f p b x₁ x₂ +
        differenceTermThree phi f p B x₁ x₂ := by
  rw [parameterIntegral_eq_shifted, parameterIntegral_eq_shifted]
  unfold differenceTermOne differenceTermTwo differenceTermThree
  have h1 (c d : ℝ) :
      IntervalIntegrable (shiftedKernel phi f p x₁) volume c d :=
    shiftedKernel_intervalIntegrable_of_continuous
      phi f p x₁ c d hp hphi
  have h2 (c d : ℝ) :
      IntervalIntegrable (shiftedKernel phi f p x₂) volume c d :=
    shiftedKernel_intervalIntegrable_of_continuous
      phi f p x₂ c d hp hphi
  rw [intervalIntegral.integral_sub (h1 _ _) (h2 _ _)]
  have hlo :=
    intervalIntegral.integral_add_adjacent_intervals
      (f := shiftedKernel phi f p x₂)
      (a := shiftedLower f b x₂)
      (b := shiftedLower f b x₁)
      (c := shiftedUpper f B x₁)
      (h2 _ _) (h2 _ _)
  have hup :=
    intervalIntegral.integral_add_adjacent_intervals
      (f := shiftedKernel phi f p x₂)
      (a := shiftedLower f b x₂)
      (b := shiftedUpper f B x₂)
      (c := shiftedUpper f B x₁)
      (h2 _ _) (h2 _ _)
  linarith

theorem gap13 (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (a A b B p x : ℝ)
    (haA : a ≤ A) (hbB : b ≤ B) (hp : p < 1)
    (hphi : ContinuousOn phi (rectangle a A b B))
    (hf : ContinuousOn f (Set.Icc a A))
    (hx : x ∈ Set.Icc a A) :
    Tendsto (parameterIntegral phi f p b B)
      (nhdsWithin x (Set.Icc a A))
      (nhds (parameterIntegral phi f p b B x)) := by
  have hrectClosed : IsClosed (rectangle a A b B) := by
    rw [rectangle_eq_prod]
    exact isClosed_Icc.prod isClosed_Icc
  let phiSub : C(rectangle a A b B, ℝ) :=
    ⟨fun z => phi z, (continuousOn_iff_continuous_restrict).mp hphi⟩
  obtain ⟨Phi, hPhi⟩ := phiSub.exists_restrict_eq hrectClosed
  have hPhiEq :
      ∀ z ∈ rectangle a A b B, Phi z = phi z := by
    intro z hz
    have h :=
      congrArg (fun g : C(rectangle a A b B, ℝ) => g ⟨z, hz⟩) hPhi
    simpa [phiSub] using h
  have hparamEq :
      ∀ z ∈ Set.Icc a A,
        parameterIntegral phi f p b B z =
          parameterIntegral Phi f p b B z := by
    intro z hz
    unfold parameterIntegral
    apply intervalIntegral.integral_congr
    intro y hy
    have hy' : y ∈ Set.Icc b B := by
      simpa [Set.uIcc_of_le hbB] using hy
    simp only [weightedKernel]
    rw [hPhiEq (z, y) ⟨hz.1, hz.2, hy'.1, hy'.2⟩]
  have ht1 :=
    gap10 Phi f a A b B p x haA hbB hp Phi.continuous hf hx
  have ht2 :=
    gap11 Phi f a A b B p x haA hbB hp Phi.continuous hf hx
  have ht3 :=
    gap12 Phi f a A b B p x haA hbB hp Phi.continuous hf hx
  have hright :
      Tendsto
        (fun z =>
          differenceTermOne Phi f p b B x z -
            differenceTermTwo Phi f p b x z +
            differenceTermThree Phi f p B x z)
        (nhdsWithin x (Set.Icc a A)) (nhds 0) := by
    convert (ht1.sub ht2).add ht3 using 1 <;> norm_num
  have hdiff :
      Tendsto
        (fun z =>
          parameterIntegral Phi f p b B x -
            parameterIntegral Phi f p b B z)
        (nhdsWithin x (Set.Icc a A)) (nhds 0) := by
    apply hright.congr'
    filter_upwards with z
    exact
      (parameter_difference_identity
        Phi f p b B x z hp Phi.continuous).symm
  have hPhiParam :
      Tendsto (parameterIntegral Phi f p b B)
        (nhdsWithin x (Set.Icc a A))
        (nhds (parameterIntegral Phi f p b B x)) := by
    have hconst :
        Tendsto
          (fun _ : ℝ => parameterIntegral Phi f p b B x)
          (nhdsWithin x (Set.Icc a A))
          (nhds (parameterIntegral Phi f p b B x)) :=
      tendsto_const_nhds
    have h := hconst.sub hdiff
    convert h using 1 <;> ring
  rw [hparamEq x hx]
  apply hPhiParam.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (hparamEq z hz).symm

theorem gap14 (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (a A b B p : ℝ)
    (haA : a ≤ A) (hbB : b ≤ B) (hp : p < 1)
    (hphi : ContinuousOn phi (rectangle a A b B))
    (hf : ContinuousOn f (Set.Icc a A)) :
    UniformContinuousOn
      (parameterIntegral phi f p b B) (Set.Icc a A) := by
  apply isCompact_Icc.uniformContinuousOn_of_continuous
  intro x hx
  exact gap13 phi f a A b B p x haA hbB hp hphi hf hx

theorem gap15 (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (a A b B p : ℝ)
    (haA : a ≤ A) (hbB : b ≤ B) (hp : p < 1)
    (hphi : ContinuousOn phi (rectangle a A b B))
    (hf : ContinuousOn f (Set.Icc a A)) :
    ContinuousOn
      (parameterIntegral phi f p b B) (Set.Icc a A) := by
  intro x hx
  exact gap13 phi f a A b B p x haA hbB hp hphi hf hx

theorem gap16 (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (a A b B p : ℝ) :
    (∫ x in a..A, ∫ y in b..B, weightedKernel phi f p x y) =
      ∫ x in a..A, parameterIntegral phi f p b B x := by
  rfl

theorem gap17 (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (a A b B p : ℝ)
    (haA : a ≤ A) (hbB : b ≤ B) (hp : p < 1)
    (hphi : ContinuousOn phi (rectangle a A b B))
    (hf : ContinuousOn f (Set.Icc a A)) :
    IntervalIntegrable
      (parameterIntegral phi f p b B) volume a A := by
  apply ContinuousOn.intervalIntegrable
  simpa [Set.uIcc_of_le haA] using
    gap15 phi f a A b B p haA hbB hp hphi hf

theorem gap18 (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (a A b B p : ℝ)
    (haA : a ≤ A) (hbB : b ≤ B) (hp : p < 1)
    (hphi : ContinuousOn phi (rectangle a A b B))
    (hf : ContinuousOn f (Set.Icc a A)) :
    IntervalIntegrable
      (fun x => ∫ y in b..B, weightedKernel phi f p x y)
      volume a A := by
  simpa [parameterIntegral] using
    gap17 phi f a A b B p haA hbB hp hphi hf

private def modelProduct
    (f : ℝ → ℝ) (p a A b B : ℝ) (q : ℝ × ℝ) : ℝ :=
  (Set.Icc a A ×ˢ Set.Icc b B).indicator
    (fun q => singularKernel p (f q.1 - q.2)) q

private theorem modelProduct_aestronglyMeasurable
    (f : ℝ → ℝ) (p a A b B : ℝ)
    (hf : ContinuousOn f (Set.Icc a A)) :
    AEStronglyMeasurable (modelProduct f p a A b B)
      ((volume : Measure ℝ).prod volume) := by
  let f₀ : ℝ → ℝ :=
    (Set.Icc a A).piecewise f (fun _ => 0)
  have hf₀ : Measurable f₀ := by
    dsimp [f₀]
    exact hf.measurable_piecewise
      continuous_const.continuousOn measurableSet_Icc
  have hraw :
      Measurable
        (fun q : ℝ × ℝ =>
          singularKernel p (f₀ q.1 - q.2)) := by
    exact (singularKernel_measurable p).comp
      ((hf₀.comp measurable_fst).sub measurable_snd)
  have hmeas :
      AEStronglyMeasurable (modelProduct f₀ p a A b B)
        ((volume : Measure ℝ).prod volume) := by
    exact (hraw.indicator
      (measurableSet_Icc.prod measurableSet_Icc)).aestronglyMeasurable
  apply hmeas.congr
  filter_upwards with q
  by_cases hq : q ∈ Set.Icc a A ×ˢ Set.Icc b B
  · have hf₀q : f₀ q.1 = f q.1 := by
      dsimp [f₀]
      simp [hq.1]
    simp only [modelProduct, Set.indicator_of_mem hq, hf₀q]
  · simp only [modelProduct, Set.indicator_of_notMem hq]

private theorem modelProduct_integrable
    (f : ℝ → ℝ) (p a A b B : ℝ)
    (haA : a ≤ A) (hbB : b ≤ B)
    (hf : ContinuousOn f (Icc a A))
    (hp : p < 1) :
    Integrable (modelProduct f p a A b B)
      ((volume : Measure ℝ).prod volume) := by
  have hmeas :=
    modelProduct_aestronglyMeasurable f p a A b B hf
  have hfbdd :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ Set.Icc a A, |f x| ≤ C := by
    have hb :
        BddAbove
          ((fun x : ℝ => |f x|) '' Set.Icc a A) :=
      isCompact_Icc.bddAbove_image hf.abs
    rcases hb with ⟨C, hC⟩
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro x hx
    exact (hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  rcases hfbdd with ⟨C, hC0, hCf⟩
  let R : ℝ := C + max |b| |B| + 1
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hbigInterval :
      IntervalIntegrable (singularKernel p) volume (-R) R :=
    singularKernel_intervalIntegrable p (-R) R hp
  have hbig :
      IntegrableOn (singularKernel p) (Set.Icc (-R) R) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le
      (neg_le_self hR.le)).mp hbigInterval
  let K : ℝ :=
    ∫ t in Set.Icc (-R) R, singularKernel p t
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun t =>
        singularKernel_nonneg p t)
  have hsections :
      ∀ᵐ x ∂(volume : Measure ℝ),
        Integrable (fun y : ℝ =>
          modelProduct f p a A b B (x, y)) volume := by
    filter_upwards with x
    by_cases hx : x ∈ Set.Icc a A
    · have hshift :
          IntervalIntegrable
            (fun y : ℝ => singularKernel p (f x - y))
            volume b B := by
        have h :=
          (singularKernel_intervalIntegrable
            p (f x - B) (f x - b) hp).comp_sub_left (f x)
        simpa using h.symm
      have hi :
          Integrable
            ((Set.Icc b B).indicator
              (fun y : ℝ => singularKernel p (f x - y)))
            volume :=
        (integrable_indicator_iff measurableSet_Icc).mpr
          ((intervalIntegrable_iff_integrableOn_Icc_of_le hbB).mp hshift)
      convert hi using 1
      funext y
      by_cases hy : y ∈ Set.Icc b B
      · have hxy :
            (x, y) ∈ Set.Icc a A ×ˢ Set.Icc b B :=
          ⟨hx, hy⟩
        rw [modelProduct, Set.indicator_of_mem hxy,
          Set.indicator_of_mem hy]
      · have hxy :
            (x, y) ∉ Set.Icc a A ×ˢ Set.Icc b B := by
          intro h
          exact hy h.2
        rw [modelProduct, Set.indicator_of_notMem hxy,
          Set.indicator_of_notMem hy]
    · have hz :
          (fun y : ℝ => modelProduct f p a A b B (x, y)) =
            (fun _ : ℝ => (0 : ℝ)) := by
        funext y
        rw [modelProduct]
        apply Set.indicator_of_notMem
        intro h
        exact hx h.1
      rw [hz]
      exact integrable_zero ℝ ℝ volume
  have houterMeas :
      AEStronglyMeasurable
        (fun x : ℝ =>
          ∫ y : ℝ, ‖modelProduct f p a A b B (x, y)‖
            ∂volume) volume :=
    hmeas.norm.integral_prod_right'
  have houterBound (x : ℝ) :
      (∫ y : ℝ, ‖modelProduct f p a A b B (x, y)‖
        ∂volume) ≤
        (Set.Icc a A).indicator (fun _ : ℝ => K) x := by
    by_cases hx : x ∈ Set.Icc a A
    · rw [Set.indicator_of_mem hx]
      have hleft : -R ≤ f x - B := by
        have hfx := hCf x hx
        have hB : |B| ≤ max |b| |B| := le_max_right _ _
        have hlow : -C ≤ f x := neg_le_of_abs_le hfx
        dsimp [R]
        linarith [le_abs_self B]
      have hright : f x - b ≤ R := by
        have hfx := hCf x hx
        have hb : |b| ≤ max |b| |B| := le_max_left _ _
        have hupp : f x ≤ C := le_of_abs_le hfx
        dsimp [R]
        linarith [neg_abs_le b]
      have hsub :
          Set.Icc (f x - B) (f x - b) ⊆ Set.Icc (-R) R := by
        intro t ht
        exact ⟨hleft.trans ht.1, ht.2.trans hright⟩
      have hmono :
          (∫ t in Set.Icc (f x - B) (f x - b),
              singularKernel p t) ≤ K := by
        dsimp [K]
        exact setIntegral_mono_set hbig
          (Filter.Eventually.of_forall fun t =>
            singularKernel_nonneg p t)
          (Filter.Eventually.of_forall hsub)
      have hsection :
          (fun y : ℝ =>
            ‖modelProduct f p a A b B (x, y)‖) =
          (Set.Icc b B).indicator
            (fun y : ℝ => singularKernel p (f x - y)) := by
        funext y
        by_cases hy : y ∈ Set.Icc b B
        · have hxy :
              (x, y) ∈ Set.Icc a A ×ˢ Set.Icc b B :=
            ⟨hx, hy⟩
          rw [modelProduct, Set.indicator_of_mem hxy,
            Set.indicator_of_mem hy, Real.norm_eq_abs,
            abs_of_nonneg (singularKernel_nonneg p (f x - y))]
        · have hxy :
              (x, y) ∉ Set.Icc a A ×ˢ Set.Icc b B := by
            intro h
            exact hy h.2
          rw [modelProduct, Set.indicator_of_notMem hxy,
            Set.indicator_of_notMem hy, norm_zero]
      rw [hsection, integral_indicator measurableSet_Icc]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      rw [← intervalIntegral.integral_of_le hbB]
      rw [intervalIntegral.integral_comp_sub_left]
      rw [intervalIntegral.integral_of_le (sub_le_sub_left hbB (f x))]
      rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
      exact hmono
    · rw [Set.indicator_of_notMem hx]
      have hz :
          (fun y : ℝ =>
            ‖modelProduct f p a A b B (x, y)‖) =
              (fun _ : ℝ => (0 : ℝ)) := by
        funext y
        rw [modelProduct]
        have hxy :
            (x, y) ∉ Set.Icc a A ×ˢ Set.Icc b B := by
          intro h
          exact hx h.1
        rw [Set.indicator_of_notMem hxy, norm_zero]
      rw [hz]
      simp
  have hmajorant :
      Integrable
        ((Set.Icc a A).indicator (fun _ : ℝ => K))
        volume := by
    exact
      (integrable_indicator_iff measurableSet_Icc).mpr
        continuous_const.integrableOn_Icc
  have houter :
      Integrable
        (fun x : ℝ =>
          ∫ y : ℝ, ‖modelProduct f p a A b B (x, y)‖
            ∂volume) volume := by
    refine hmajorant.mono' houterMeas ?_
    filter_upwards with x
    have hnonneg :
        0 ≤
          (∫ y : ℝ,
            ‖modelProduct f p a A b B (x, y)‖ ∂volume) :=
      integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun y => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact houterBound x
  exact (integrable_prod_iff hmeas).mpr ⟨hsections, houter⟩

theorem gap19 (phi : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (a A b B p : ℝ)
    (haA : a ≤ A) (hbB : b ≤ B) (hp : p < 1)
    (hphi : ContinuousOn phi (rectangle a A b B))
    (hf : ContinuousOn f (Set.Icc a A)) :
    IntegrableOn
      (fun z => weightedKernel phi f p z.1 z.2)
      (rectangle a A b B) := by
  have hrectMeas :
      MeasurableSet (rectangle a A b B) := by
    rw [rectangle_eq_prod]
    exact measurableSet_Icc.prod measurableSet_Icc
  have hrectCompact :
      IsCompact (rectangle a A b B) :=
    rectangle_compact a A b B
  have hphiBdd :
      ∃ D : ℝ, 0 ≤ D ∧
        ∀ q ∈ rectangle a A b B, |phi q| ≤ D := by
    have hb :
        BddAbove
          ((fun q : ℝ × ℝ => |phi q|) ''
            rectangle a A b B) :=
      hrectCompact.bddAbove_image hphi.abs
    rcases hb with ⟨D, hD⟩
    refine ⟨max D 0, le_max_right _ _, ?_⟩
    intro q hq
    exact (hD ⟨q, hq, rfl⟩).trans (le_max_left _ _)
  rcases hphiBdd with ⟨D, hD0, hDphi⟩
  have hmodel :
      Integrable (modelProduct f p a A b B)
        ((volume : Measure ℝ).prod volume) :=
    modelProduct_integrable f p a A b B haA hbB hf hp
  have hphiInd :
      AEStronglyMeasurable
        ((rectangle a A b B).indicator phi)
        ((volume : Measure ℝ).prod volume) := by
    apply (aestronglyMeasurable_indicator_iff hrectMeas).mpr
    exact hphi.aestronglyMeasurable hrectMeas
  have hphiIndBound :
      ∀ᵐ q ∂((volume : Measure ℝ).prod volume),
        ‖(rectangle a A b B).indicator phi q‖ ≤ D := by
    filter_upwards with q
    by_cases hq : q ∈ rectangle a A b B
    · rw [Set.indicator_of_mem hq, Real.norm_eq_abs]
      exact hDphi q hq
    · rw [Set.indicator_of_notMem hq, norm_zero]
      exact hD0
  have hweighted :
      Integrable
        (fun q : ℝ × ℝ =>
          (rectangle a A b B).indicator phi q *
            modelProduct f p a A b B q)
        ((volume : Measure ℝ).prod volume) :=
    hmodel.bdd_mul hphiInd hphiIndBound
  have hindicatorEq :
      (rectangle a A b B).indicator
          (fun z => weightedKernel phi f p z.1 z.2) =
        (fun q : ℝ × ℝ =>
          (rectangle a A b B).indicator phi q *
            modelProduct f p a A b B q) := by
    funext q
    by_cases hq : q ∈ rectangle a A b B
    · have hq' :
          q ∈ Set.Icc a A ×ˢ Set.Icc b B := by
        rw [← rectangle_eq_prod]
        exact hq
      rw [Set.indicator_of_mem hq,
        Set.indicator_of_mem hq, modelProduct,
        Set.indicator_of_mem hq']
      simp only [weightedKernel, singularKernel, div_eq_mul_inv,
        one_div, one_mul]
    · have hq' :
          q ∉ Set.Icc a A ×ˢ Set.Icc b B := by
        rw [← rectangle_eq_prod]
        exact hq
      rw [Set.indicator_of_notMem hq,
        Set.indicator_of_notMem hq, modelProduct,
        Set.indicator_of_notMem hq', zero_mul]
  apply (integrable_indicator_iff hrectMeas).mp
  rw [Measure.volume_eq_prod, hindicatorEq]
  exact hweighted

end

end ProofGap.Exercise4186
