import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4150

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def ball (R : ℝ) : Set Point3 :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ R ^ 2}

def radialDensity (k : ℝ) (p : Point3) : ℝ :=
  k * Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)

def mass (R k : ℝ) : ℝ :=
  ∫ p in ball R, radialDensity k p

def inertiaZ (R k : ℝ) : ℝ :=
  ∫ p in ball R, (p.1 ^ 2 + p.2.1 ^ 2) * radialDensity k p

private def baseIntegrand (B : ℝ → ℝ → ℝ) (p : Point3) : ℝ :=
  B (Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2))
    (Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2))

private def ballIntegrand (R : ℝ) (B : ℝ → ℝ → ℝ) (p : Point3) : ℝ :=
  (ball R).indicator (baseIntegrand B) p

private def verticalIntegral (R : ℝ) (B : ℝ → ℝ → ℝ)
    (xy : ℝ × ℝ) : ℝ :=
  ∫ z : ℝ, ballIntegrand R B (xy.1, xy.2, z)

private def halfDisk (R : ℝ) : Set (ℝ × ℝ) :=
  {w | 0 < w.1 ∧ w.1 ^ 2 + w.2 ^ 2 ≤ R ^ 2}

private def planeBase (B : ℝ → ℝ → ℝ) (w : ℝ × ℝ) : ℝ :=
  w.1 * B w.1 (Real.sqrt (w.1 ^ 2 + w.2 ^ 2))

private def planeIntegrand (R : ℝ) (B : ℝ → ℝ → ℝ)
    (w : ℝ × ℝ) : ℝ :=
  (halfDisk R).indicator (planeBase B) w

private def sphericalBase (B : ℝ → ℝ → ℝ)
    (v : ℝ × ℝ) : ℝ :=
  v.1 ^ 2 * Real.cos v.2 * B (v.1 * Real.cos v.2) v.1

private theorem ball_measurable (R : ℝ) :
    MeasurableSet (ball R) := by
  unfold ball
  measurability

private theorem halfDisk_measurable (R : ℝ) :
    MeasurableSet (halfDisk R) := by
  unfold halfDisk
  measurability

private theorem ball_subset_box (R : ℝ) (hR : 0 < R) :
    ball R ⊆
      Set.Icc (-R) R ×ˢ
        (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) := by
  intro p hp
  rcases p with ⟨x, y, z⟩
  change x ^ 2 + y ^ 2 + z ^ 2 ≤ R ^ 2 at hp
  have hx₀ : -R ≤ x := by
    nlinarith [sq_nonneg y, sq_nonneg z, sq_nonneg (x + R)]
  have hx₁ : x ≤ R := by
    nlinarith [sq_nonneg y, sq_nonneg z, sq_nonneg (x - R)]
  have hy₀ : -R ≤ y := by
    nlinarith [sq_nonneg x, sq_nonneg z, sq_nonneg (y + R)]
  have hy₁ : y ≤ R := by
    nlinarith [sq_nonneg x, sq_nonneg z, sq_nonneg (y - R)]
  have hz₀ : -R ≤ z := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (z + R)]
  have hz₁ : z ≤ R := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (z - R)]
  exact ⟨⟨hx₀, hx₁⟩, ⟨⟨hy₀, hy₁⟩, hz₀, hz₁⟩⟩

private theorem ballIntegrand_integrable
    (R : ℝ) (hR : 0 < R) (B : ℝ → ℝ → ℝ)
    (hB : Continuous (Function.uncurry B)) :
    Integrable (ballIntegrand R B) := by
  have hbase : Continuous (baseIntegrand B) := by
    unfold baseIntegrand
    exact hB.comp
      ((Real.continuous_sqrt.comp
          ((continuous_fst.pow 2).add
            ((continuous_fst.comp continuous_snd).pow 2))).prodMk
        (Real.continuous_sqrt.comp
          (((continuous_fst.pow 2).add
            ((continuous_fst.comp continuous_snd).pow 2)).add
              ((continuous_snd.comp continuous_snd).pow 2))))
  have hcompact :
      IsCompact
        (Set.Icc (-R) R ×ˢ
          (Set.Icc (-R) R ×ˢ Set.Icc (-R) R)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hi : IntegrableOn (baseIntegrand B)
      (Set.Icc (-R) R ×ˢ
        (Set.Icc (-R) R ×ˢ Set.Icc (-R) R)) :=
    hbase.continuousOn.integrableOn_compact hcompact
  unfold ballIntegrand
  exact (integrable_indicator_iff (ball_measurable R)).2
    (hi.mono_set (ball_subset_box R hR))

private theorem halfDisk_subset_box (R : ℝ) (hR : 0 < R) :
    halfDisk R ⊆
      Set.Icc (0 : ℝ) R ×ˢ Set.Icc (-R) R := by
  intro w hw
  change 0 < w.1 ∧ w.1 ^ 2 + w.2 ^ 2 ≤ R ^ 2 at hw
  have hρ₁ : w.1 ≤ R := by
    nlinarith [hw.2, sq_nonneg w.2, sq_nonneg (w.1 - R)]
  have hz₀ : -R ≤ w.2 := by
    nlinarith [hw.2, sq_nonneg w.1, sq_nonneg (w.2 + R)]
  have hz₁ : w.2 ≤ R := by
    nlinarith [hw.2, sq_nonneg w.1, sq_nonneg (w.2 - R)]
  exact ⟨⟨hw.1.le, hρ₁⟩, hz₀, hz₁⟩

private theorem planeIntegrand_integrable
    (R : ℝ) (hR : 0 < R) (B : ℝ → ℝ → ℝ)
    (hB : Continuous (Function.uncurry B)) :
    Integrable (planeIntegrand R B) := by
  have hbase : Continuous (planeBase B) := by
    unfold planeBase
    apply continuous_fst.mul
    exact hB.comp
      (continuous_fst.prodMk
        (Real.continuous_sqrt.comp
          ((continuous_fst.pow 2).add (continuous_snd.pow 2))))
  have hcompact :
      IsCompact
        (Set.Icc (0 : ℝ) R ×ˢ Set.Icc (-R) R) :=
    isCompact_Icc.prod isCompact_Icc
  have hi : IntegrableOn (planeBase B)
      (Set.Icc (0 : ℝ) R ×ˢ Set.Icc (-R) R) :=
    hbase.continuousOn.integrableOn_compact hcompact
  unfold planeIntegrand
  exact (integrable_indicator_iff (halfDisk_measurable R)).2
    (hi.mono_set (halfDisk_subset_box R hR))

private theorem firstPolar_pointwise
    (R : ℝ) (B : ℝ → ℝ → ℝ)
    (u : ℝ × ℝ) (hu : u ∈ polarCoord.target) :
    u.1 * verticalIntegral R B (polarCoord.symm u) =
      ∫ z : ℝ, planeIntegrand R B (u.1, z) := by
  have hrpos : 0 < u.1 := hu.1
  have hsq :
      (polarCoord.symm u).1 ^ 2 +
          (polarCoord.symm u).2 ^ 2 = u.1 ^ 2 := by
    simp only [polarCoord_symm_apply]
    nlinarith [Real.sin_sq_add_cos_sq u.2]
  have hsqrt : Real.sqrt (u.1 ^ 2) = u.1 := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hrpos]
  calc
    u.1 * verticalIntegral R B (polarCoord.symm u) =
        ∫ z : ℝ,
          u.1 * ballIntegrand R B
            ((polarCoord.symm u).1, (polarCoord.symm u).2, z) := by
      unfold verticalIntegral
      rw [MeasureTheory.integral_const_mul]
    _ = ∫ z : ℝ, planeIntegrand R B (u.1, z) := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hm :
          ((polarCoord.symm u).1,
            (polarCoord.symm u).2, z) ∈ ball R
      · have hm' : (u.1, z) ∈ halfDisk R := by
          constructor
          · exact hrpos
          · change u.1 ^ 2 + z ^ 2 ≤ R ^ 2
            change
              (polarCoord.symm u).1 ^ 2 +
                (polarCoord.symm u).2 ^ 2 + z ^ 2 ≤ R ^ 2 at hm
            rwa [hsq] at hm
        rw [ballIntegrand, Set.indicator_of_mem hm,
          planeIntegrand, Set.indicator_of_mem hm']
        unfold baseIntegrand planeBase
        rw [hsq, hsqrt]
      · have hm' : (u.1, z) ∉ halfDisk R := by
          intro h
          apply hm
          change
            (polarCoord.symm u).1 ^ 2 +
              (polarCoord.symm u).2 ^ 2 + z ^ 2 ≤ R ^ 2
          rw [hsq]
          exact h.2
        rw [ballIntegrand, Set.indicator_of_notMem hm,
          planeIntegrand, Set.indicator_of_notMem hm']
        simp

private theorem cos_pos_iff_mem_half_angle
    (ψ : ℝ) (hψ : ψ ∈ Set.Ioo (-Real.pi) Real.pi) :
    0 < Real.cos ψ ↔
      ψ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  constructor
  · intro hc
    constructor
    · by_contra h
      have hle : ψ ≤ -(Real.pi / 2) := le_of_not_gt h
      have hnonpos : Real.cos (-ψ) ≤ 0 := by
        apply Real.cos_nonpos_of_pi_div_two_le_of_le
        · linarith
        · have hnegψ : -ψ < Real.pi := by
            linarith [hψ.1]
          linarith [Real.pi_pos]
      rw [Real.cos_neg] at hnonpos
      linarith
    · by_contra h
      have hle : Real.pi / 2 ≤ ψ := le_of_not_gt h
      have hnonpos : Real.cos ψ ≤ 0 := by
        apply Real.cos_nonpos_of_pi_div_two_le_of_le
        · exact hle
        · linarith [hψ.2, Real.pi_pos]
      linarith
  · exact Real.cos_pos_of_mem_Ioo

private theorem secondPolar_mem_iff
    (R : ℝ) (hR : 0 < R)
    (v : ℝ × ℝ) (hv : v ∈ polarCoord.target) :
    polarCoord.symm v ∈ halfDisk R ↔
      v ∈ Set.Ioc (0 : ℝ) R ×ˢ
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  have hrpos : 0 < v.1 := hv.1
  have hsq :
      (polarCoord.symm v).1 ^ 2 +
          (polarCoord.symm v).2 ^ 2 = v.1 ^ 2 := by
    simp only [polarCoord_symm_apply]
    nlinarith [Real.sin_sq_add_cos_sq v.2]
  constructor
  · intro hm
    have hc : 0 < Real.cos v.2 := by
      have hmρ := hm.1
      change 0 < v.1 * Real.cos v.2 at hmρ
      rcases (mul_pos_iff.mp hmρ) with hpos | hneg
      · exact hpos.2
      · linarith
    have hrle : v.1 ≤ R := by
      have hrsq : v.1 ^ 2 ≤ R ^ 2 := by
        rw [← hsq]
        exact hm.2
      nlinarith [sq_nonneg (v.1 - R)]
    exact ⟨⟨hrpos, hrle⟩,
      (cos_pos_iff_mem_half_angle v.2 hv.2).1 hc⟩
  · intro hm
    have hc : 0 < Real.cos v.2 :=
      Real.cos_pos_of_mem_Ioo hm.2
    constructor
    · change 0 < v.1 * Real.cos v.2
      positivity
    · rw [hsq]
      nlinarith [mul_nonneg hm.1.1.le
        (sub_nonneg.mpr hm.1.2)]

private theorem secondPolar_pointwise
    (R : ℝ) (hR : 0 < R) (B : ℝ → ℝ → ℝ)
    (v : ℝ × ℝ) (hv : v ∈ polarCoord.target) :
    v.1 * planeIntegrand R B (polarCoord.symm v) =
      (Set.Ioc (0 : ℝ) R ×ˢ
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)).indicator
          (sphericalBase B) v := by
  have hrpos : 0 < v.1 := hv.1
  have hsq :
      (polarCoord.symm v).1 ^ 2 +
          (polarCoord.symm v).2 ^ 2 = v.1 ^ 2 := by
    simp only [polarCoord_symm_apply]
    nlinarith [Real.sin_sq_add_cos_sq v.2]
  have hsqrt : Real.sqrt (v.1 ^ 2) = v.1 := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hrpos]
  by_cases hm : polarCoord.symm v ∈ halfDisk R
  · have hm' := (secondPolar_mem_iff R hR v hv).1 hm
    rw [planeIntegrand, Set.indicator_of_mem hm,
      Set.indicator_of_mem hm']
    unfold planeBase sphericalBase
    simp only [polarCoord_symm_apply]
    have hsq' :
        (v.1 * Real.cos v.2) ^ 2 +
          (v.1 * Real.sin v.2) ^ 2 = v.1 ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq v.2]
    rw [hsq', hsqrt]
    ring
  · have hm' : v ∉ Set.Ioc (0 : ℝ) R ×ˢ
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      intro h
      exact hm ((secondPolar_mem_iff R hR v hv).2 h)
    rw [planeIntegrand, Set.indicator_of_notMem hm,
      Set.indicator_of_notMem hm']
    simp

private theorem radialVertical_eq_plane
    (R : ℝ) (hR : 0 < R) (B : ℝ → ℝ → ℝ)
    (hB : Continuous (Function.uncurry B)) :
    (∫ ρ in Set.Ioi (0 : ℝ),
        ∫ z : ℝ, planeIntegrand R B (ρ, z)) =
      ∫ w : ℝ × ℝ, planeIntegrand R B w := by
  have hi := planeIntegrand_integrable R hR B hB
  have hi' : Integrable (planeIntegrand R B)
      (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hi
  have hfubini :
      (∫ w : ℝ × ℝ, planeIntegrand R B w) =
        ∫ ρ : ℝ, ∫ z : ℝ, planeIntegrand R B (ρ, z) := by
    change
      (∫ w : ℝ × ℝ, planeIntegrand R B w
        ∂volume.prod volume) = _
    rw [MeasureTheory.integral_prod _ hi']
  rw [hfubini]
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with ρ
  by_cases hρ : ρ ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hρ]
  · rw [Set.indicator_of_notMem hρ]
    rw [← integral_zero]
    apply integral_congr_ae
    filter_upwards with z
    have hm : (ρ, z) ∉ halfDisk R := by
      intro h
      exact hρ h.1
    rw [planeIntegrand, Set.indicator_of_notMem hm]

private theorem planeIntegral_eq_spherical
    (R : ℝ) (hR : 0 < R) (B : ℝ → ℝ → ℝ)
    (hB : Continuous (Function.uncurry B)) :
    (∫ w : ℝ × ℝ, planeIntegrand R B w) =
      ∫ ψ in -Real.pi / 2..Real.pi / 2,
        ∫ r in (0 : ℝ)..R,
          sphericalBase B (r, ψ) := by
  rw [← integral_comp_polarCoord_symm]
  let rect : Set (ℝ × ℝ) :=
    Set.Ioc (0 : ℝ) R ×ˢ
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
  have htarget : MeasurableSet polarCoord.target :=
    polarCoord.open_target.measurableSet
  have hrect : MeasurableSet rect :=
    measurableSet_Ioc.prod measurableSet_Ioo
  have hrestrict :
      (∫ v in polarCoord.target,
          v.1 * planeIntegrand R B (polarCoord.symm v)) =
        ∫ v in rect, sphericalBase B v := by
    rw [← integral_indicator htarget,
      ← integral_indicator hrect]
    apply integral_congr_ae
    filter_upwards with v
    by_cases hv : v ∈ polarCoord.target
    · rw [Set.indicator_of_mem hv]
      exact secondPolar_pointwise R hR B v hv
    · rw [Set.indicator_of_notMem hv]
      have hvr : v ∉ rect := by
        intro h
        apply hv
        refine ⟨?_, ?_⟩
        · change 0 < v.1
          exact h.1.1
        · constructor <;>
            linarith [h.2.1, h.2.2, Real.pi_pos]
      rw [Set.indicator_of_notMem hvr]
  simp only [smul_eq_mul]
  rw [hrestrict]
  have hswap :=
    MeasureTheory.setIntegral_prod_swap
      (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))
      (Set.Ioc (0 : ℝ) R)
      (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))
      (sphericalBase B)
  change
    (∫ v in Set.Ioc (0 : ℝ) R ×ˢ
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
        sphericalBase B v ∂(volume.prod volume)) =
      ∫ ψ in -Real.pi / 2..Real.pi / 2,
        ∫ r in (0 : ℝ)..R, sphericalBase B (r, ψ)
  rw [← hswap]
  have hcontSwap : Continuous
      (fun z : ℝ × ℝ => sphericalBase B (z.2, z.1)) := by
    unfold sphericalBase
    fun_prop
  have hcompactSwap :
      IsCompact
        (Set.Icc (-(Real.pi / 2)) (Real.pi / 2) ×ˢ
          Set.Icc (0 : ℝ) R) :=
    isCompact_Icc.prod isCompact_Icc
  have hsubsetSwap :
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ×ˢ
          Set.Ioc (0 : ℝ) R ⊆
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) ×ˢ
          Set.Icc (0 : ℝ) R := by
    intro z hz
    exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2⟩⟩
  have hiSwap : IntegrableOn
      (fun z : ℝ × ℝ => sphericalBase B (z.2, z.1))
      (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ×ˢ
        Set.Ioc (0 : ℝ) R) (volume.prod volume) := by
    have hi : IntegrableOn
        (fun z : ℝ × ℝ => sphericalBase B (z.2, z.1))
        (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ×ˢ
          Set.Ioc (0 : ℝ) R) :=
      (hcontSwap.continuousOn.integrableOn_compact hcompactSwap).mono_set
        hsubsetSwap
    simpa only [Measure.volume_eq_prod] using hi
  change
    (∫ z in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ×ˢ
        Set.Ioc (0 : ℝ) R,
        sphericalBase B (z.2, z.1) ∂(volume.prod volume)) =
      ∫ ψ in -Real.pi / 2..Real.pi / 2,
        ∫ r in (0 : ℝ)..R, sphericalBase B (r, ψ)
  rw [MeasureTheory.setIntegral_prod _ hiSwap]
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  simp_rw [intervalIntegral.integral_of_le hR.le]
  apply setIntegral_congr_set
  simpa only [neg_div] using
    (Ioo_ae_eq_Ioc :
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) =ᵐ[volume]
        Set.Ioc (-(Real.pi / 2)) (Real.pi / 2))

private theorem spherical_change
    (R : ℝ) (hR : 0 < R) (B : ℝ → ℝ → ℝ)
    (hB : Continuous (Function.uncurry B)) :
    (∫ p in ball R, baseIntegrand B p) =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ ψ in -Real.pi / 2..Real.pi / 2,
          ∫ r in (0 : ℝ)..R,
            sphericalBase B (r, ψ) := by
  have hg := ballIntegrand_integrable R hR B hB
  have hgassoc :
      Integrable
        (ballIntegrand R B ∘
          (MeasurableEquiv.prodAssoc :
            (ℝ × ℝ) × ℝ ≃ᵐ Point3)) :=
    (volume_preserving_prodAssoc.integrable_comp_emb
      MeasurableEquiv.prodAssoc.measurableEmbedding).2 hg
  have hfubini :
      (∫ q : (ℝ × ℝ) × ℝ,
          ballIntegrand R B (MeasurableEquiv.prodAssoc q)) =
        ∫ xy : ℝ × ℝ, verticalIntegral R B xy := by
    have hgassoc' : Integrable
        (fun q : (ℝ × ℝ) × ℝ =>
          ballIntegrand R B (MeasurableEquiv.prodAssoc q))
        (volume.prod volume) := by
      simpa only [Measure.volume_eq_prod] using hgassoc
    change
      (∫ q : (ℝ × ℝ) × ℝ,
          ballIntegrand R B (MeasurableEquiv.prodAssoc q)
            ∂volume.prod volume) =
        ∫ xy : ℝ × ℝ, verticalIntegral R B xy
    rw [MeasureTheory.integral_prod _ hgassoc']
    rfl
  have hassoc :
      (∫ q : (ℝ × ℝ) × ℝ,
          ballIntegrand R B (MeasurableEquiv.prodAssoc q)) =
        ∫ p : Point3, ballIntegrand R B p :=
    volume_preserving_prodAssoc.integral_comp
      MeasurableEquiv.prodAssoc.measurableEmbedding
        (ballIntegrand R B)
  have hfirst :
      (∫ xy : ℝ × ℝ, verticalIntegral R B xy) =
        ∫ u in polarCoord.target,
          u.1 * verticalIntegral R B (polarCoord.symm u) := by
    simpa only [smul_eq_mul] using
      (integral_comp_polarCoord_symm (verticalIntegral R B)).symm
  have hpoint :
      (∫ u in polarCoord.target,
          u.1 * verticalIntegral R B (polarCoord.symm u)) =
        ∫ u in polarCoord.target,
          ∫ z : ℝ, planeIntegrand R B (u.1, z) := by
    apply setIntegral_congr_fun
      polarCoord.open_target.measurableSet
    intro u hu
    exact firstPolar_pointwise R B u hu
  have hfactor :
      (∫ u in polarCoord.target,
          ∫ z : ℝ, planeIntegrand R B (u.1, z)) =
        (2 * Real.pi) *
          ∫ ρ in Set.Ioi (0 : ℝ),
            ∫ z : ℝ, planeIntegrand R B (ρ, z) := by
    have hangle :
        (∫ _φ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
          2 * Real.pi := by
      rw [setIntegral_const,
        Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
      simp only [smul_eq_mul]
      ring
    change
      (∫ u in Set.Ioi (0 : ℝ) ×ˢ
          Set.Ioo (-Real.pi) Real.pi,
        ∫ z : ℝ, planeIntegrand R B (u.1, z)) = _
    rw [Measure.volume_eq_prod]
    rw [show
      (∫ u in Set.Ioi (0 : ℝ) ×ˢ
          Set.Ioo (-Real.pi) Real.pi,
          (∫ z : ℝ, planeIntegrand R B (u.1, z))
            ∂(volume.prod volume)) =
        (∫ ρ in Set.Ioi (0 : ℝ),
            ∫ z : ℝ, planeIntegrand R B (ρ, z)) *
          ∫ _φ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) by
        simpa only [mul_one] using
          (MeasureTheory.setIntegral_prod_mul
            (μ := volume) (ν := volume)
            (fun ρ : ℝ =>
              ∫ z : ℝ, planeIntegrand R B (ρ, z))
            (fun _φ : ℝ => (1 : ℝ))
            (Set.Ioi (0 : ℝ))
            (Set.Ioo (-Real.pi) Real.pi))]
    rw [hangle]
    ring
  have hspherical :=
    planeIntegral_eq_spherical R hR B hB
  have houter :
      (∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ ψ in -Real.pi / 2..Real.pi / 2,
            ∫ r in (0 : ℝ)..R,
              sphericalBase B (r, ψ)) =
        (2 * Real.pi) *
          ∫ ψ in -Real.pi / 2..Real.pi / 2,
            ∫ r in (0 : ℝ)..R,
              sphericalBase B (r, ψ) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  calc
    (∫ p in ball R, baseIntegrand B p) =
        ∫ p : Point3, ballIntegrand R B p := by
      unfold ballIntegrand
      rw [integral_indicator (ball_measurable R)]
    _ = ∫ q : (ℝ × ℝ) × ℝ,
          ballIntegrand R B (MeasurableEquiv.prodAssoc q) :=
      hassoc.symm
    _ = ∫ xy : ℝ × ℝ, verticalIntegral R B xy := hfubini
    _ = ∫ u in polarCoord.target,
          u.1 * verticalIntegral R B (polarCoord.symm u) := hfirst
    _ = ∫ u in polarCoord.target,
          ∫ z : ℝ, planeIntegrand R B (u.1, z) := hpoint
    _ = (2 * Real.pi) *
          ∫ ρ in Set.Ioi (0 : ℝ),
            ∫ z : ℝ, planeIntegrand R B (ρ, z) := hfactor
    _ = (2 * Real.pi) *
          ∫ w : ℝ × ℝ, planeIntegrand R B w := by
      rw [radialVertical_eq_plane R hR B hB]
    _ = (2 * Real.pi) *
          ∫ ψ in -Real.pi / 2..Real.pi / 2,
            ∫ r in (0 : ℝ)..R,
              sphericalBase B (r, ψ) := by
      rw [hspherical]
    _ = ∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ ψ in -Real.pi / 2..Real.pi / 2,
            ∫ r in (0 : ℝ)..R,
              sphericalBase B (r, ψ) :=
      houter.symm

theorem gap1 (R k : ℝ) (hR : 0 < R) :
    mass R k =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ ψ in -Real.pi / 2..Real.pi / 2,
          ∫ r in (0 : ℝ)..R,
            r ^ 2 * Real.cos ψ * (k * r) := by
  simpa [mass, radialDensity, baseIntegrand, sphericalBase] using
    (spherical_change R hR (fun _ρ r => k * r) (by fun_prop))

theorem gap2 (R k : ℝ) (hR : 0 < R) :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ ψ in -Real.pi / 2..Real.pi / 2,
          ∫ r in (0 : ℝ)..R,
            r ^ 2 * Real.cos ψ * (k * r)) =
      k * Real.pi * R ^ 4 := by
  have hr (ψ : ℝ) :
      (∫ r in (0 : ℝ)..R,
          r ^ 2 * Real.cos ψ * (k * r)) =
        Real.cos ψ * (k * R ^ 4 / 4) := by
    calc
      (∫ r in (0 : ℝ)..R,
          r ^ 2 * Real.cos ψ * (k * r)) =
          Real.cos ψ * k * (∫ r in (0 : ℝ)..R, r ^ 3) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro r _
        ring
      _ = Real.cos ψ * (k * R ^ 4 / 4) := by
        rw [integral_pow]
        norm_num
        ring
  have hcos :
      (∫ ψ in -Real.pi / 2..Real.pi / 2, Real.cos ψ) = 2 := by
    calc
      (∫ ψ in -Real.pi / 2..Real.pi / 2, Real.cos ψ) =
          Real.sin (Real.pi / 2) - Real.sin (-Real.pi / 2) := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x _ => Real.hasDerivAt_sin x)
        exact Real.continuous_cos.intervalIntegrable _ _
      _ = 2 := by
        rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
          Real.sin_neg, Real.sin_pi_div_two]
        norm_num
  simp_rw [hr]
  rw [intervalIntegral.integral_mul_const, hcos,
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

theorem gap3 (R k : ℝ) (hR : 0 < R) :
    mass R k = k * Real.pi * R ^ 4 := by
  rw [gap1 R k hR, gap2 R k hR]

theorem gap4 (R k : ℝ) (hR : 0 < R) :
    k = mass R k / (Real.pi * R ^ 4) := by
  rw [gap3 R k hR]
  field_simp [Real.pi_ne_zero, ne_of_gt hR]

theorem gap5 (R k r : ℝ) (hR : 0 < R) :
    k * r = mass R k * r / (Real.pi * R ^ 4) := by
  calc
    k * r = (mass R k / (Real.pi * R ^ 4)) * r := by
      exact congrArg (fun c : ℝ => c * r) (gap4 R k hR)
    _ = mass R k * r / (Real.pi * R ^ 4) := by ring

theorem gap6 (R k : ℝ) (hR : 0 < R) :
    inertiaZ R k =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ ψ in -Real.pi / 2..Real.pi / 2,
          ∫ r in (0 : ℝ)..R,
            r ^ 2 * Real.cos ψ ^ 2 *
              (mass R k * r ^ 3 / (Real.pi * R ^ 4)) *
                Real.cos ψ := by
  have hs := spherical_change R hR
    (fun ρ r => ρ ^ 2 * (k * r)) (by fun_prop)
  calc
    inertiaZ R k =
        ∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ ψ in -Real.pi / 2..Real.pi / 2,
            ∫ r in (0 : ℝ)..R,
              sphericalBase (fun ρ r => ρ ^ 2 * (k * r))
                (r, ψ) := by
      rw [← hs]
      unfold inertiaZ radialDensity baseIntegrand
      apply setIntegral_congr_fun (ball_measurable R)
      intro p _
      change
        (p.1 ^ 2 + p.2.1 ^ 2) *
            (k * Real.sqrt
              (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)) =
          Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2) ^ 2 *
            (k * Real.sqrt
              (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2))
      rw [Real.sq_sqrt (by positivity :
        0 ≤ p.1 ^ 2 + p.2.1 ^ 2)]
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro φ _
      apply intervalIntegral.integral_congr
      intro ψ _
      apply intervalIntegral.integral_congr
      intro r _
      unfold sphericalBase
      change
        r ^ 2 * Real.cos ψ *
            ((r * Real.cos ψ) ^ 2 * (k * r)) =
          r ^ 2 * Real.cos ψ ^ 2 *
            (mass R k * r ^ 3 / (Real.pi * R ^ 4)) *
              Real.cos ψ
      rw [← gap5 R k (r ^ 3) hR]
      ring

theorem gap7 (R k : ℝ) (hR : 0 < R) :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ ψ in -Real.pi / 2..Real.pi / 2,
          ∫ r in (0 : ℝ)..R,
            r ^ 2 * Real.cos ψ ^ 2 *
              (mass R k * r ^ 3 / (Real.pi * R ^ 4)) *
                Real.cos ψ) =
      2 * mass R k / R ^ 4 *
        (∫ ψ in -Real.pi / 2..Real.pi / 2, Real.cos ψ ^ 3) *
          ∫ r in (0 : ℝ)..R, r ^ 5 := by
  have hinner (ψ : ℝ) :
      (∫ r in (0 : ℝ)..R,
          r ^ 2 * Real.cos ψ ^ 2 *
            (mass R k * r ^ 3 / (Real.pi * R ^ 4)) *
              Real.cos ψ) =
        (mass R k / (Real.pi * R ^ 4)) *
          Real.cos ψ ^ 3 *
            ∫ r in (0 : ℝ)..R, r ^ 5 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    ring
  have hmiddle :
      (∫ ψ in -Real.pi / 2..Real.pi / 2,
          (mass R k / (Real.pi * R ^ 4)) *
            Real.cos ψ ^ 3 *
              ∫ r in (0 : ℝ)..R, r ^ 5) =
        (mass R k / (Real.pi * R ^ 4)) *
          (∫ ψ in -Real.pi / 2..Real.pi / 2,
            Real.cos ψ ^ 3) *
            ∫ r in (0 : ℝ)..R, r ^ 5 := by
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const_mul]
  simp_rw [hinner]
  rw [hmiddle, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  field_simp [Real.pi_ne_zero, ne_of_gt hR]

theorem gap8 (R k : ℝ) (hR : 0 < R) :
    2 * mass R k / R ^ 4 *
        (∫ ψ in -Real.pi / 2..Real.pi / 2, Real.cos ψ ^ 3) *
          (∫ r in (0 : ℝ)..R, r ^ 5) =
      4 * mass R k * R ^ 2 / 9 := by
  have hcos :
      (∫ ψ in -Real.pi / 2..Real.pi / 2, Real.cos ψ) = 2 := by
    calc
      (∫ ψ in -Real.pi / 2..Real.pi / 2, Real.cos ψ) =
          Real.sin (Real.pi / 2) - Real.sin (-Real.pi / 2) := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x _ => Real.hasDerivAt_sin x)
        exact Real.continuous_cos.intervalIntegrable _ _
      _ = 2 := by
        rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
          Real.sin_neg, Real.sin_pi_div_two]
        norm_num
  have hcos3 :
      (∫ ψ in -Real.pi / 2..Real.pi / 2,
          Real.cos ψ ^ 3) = 4 / 3 := by
    change
      (∫ ψ in -Real.pi / 2..Real.pi / 2,
        Real.cos ψ ^ (1 + 2)) = 4 / 3
    rw [integral_cos_pow]
    simp only [pow_one]
    rw [hcos]
    rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
      Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    norm_num
  have hr5 :
      (∫ r in (0 : ℝ)..R, r ^ 5) = R ^ 6 / 6 := by
    rw [integral_pow]
    norm_num
  rw [hcos3, hr5]
  field_simp [ne_of_gt hR]
  ring

theorem gap9 (R k : ℝ) (hR : 0 < R) :
    inertiaZ R k = 4 * mass R k * R ^ 2 / 9 := by
  rw [gap6 R k hR, gap7 R k hR, gap8 R k hR]

end

end ProofGap.Exercise4150
