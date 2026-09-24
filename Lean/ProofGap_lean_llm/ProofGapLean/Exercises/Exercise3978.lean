import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.MeanValue
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Instances.Real.Lemmas

namespace ProofGap.Exercise3978

noncomputable section

open Filter MeasureTheory
open scoped Topology

def disk (ρ : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ ρ ^ 2}

def diskIntegral (f : (ℝ × ℝ) → ℝ) (ρ : ℝ) : ℝ :=
  ∫ p in disk ρ, f p

def IsMeanPoint (f : (ℝ × ℝ) → ℝ) (ρ : ℝ) (p : ℝ × ℝ) : Prop :=
  p ∈ disk ρ ∧ diskIntegral f ρ = Real.pi * ρ ^ 2 * f p

def meanPoint (f : (ℝ × ℝ) → ℝ) (ρ : ℝ) : ℝ × ℝ :=
  by
    classical
    exact if h : ∃ p, IsMeanPoint f ρ p then Classical.choose h else (0, 0)

def diskAverage (f : (ℝ × ℝ) → ℝ) (ρ : ℝ) : ℝ :=
  1 / (Real.pi * ρ ^ 2) * diskIntegral f ρ

private theorem measurableSet_disk (ρ : ℝ) :
    MeasurableSet (disk ρ) := by
  change
    MeasurableSet
      ((fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) ⁻¹' Set.Iic (ρ ^ 2))
  exact
    ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2))
      measurableSet_Iic

private theorem isClosed_disk (ρ : ℝ) :
    IsClosed (disk ρ) := by
  change
    IsClosed
      ((fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) ⁻¹' Set.Iic (ρ ^ 2))
  exact
    isClosed_Iic.preimage
      ((continuous_fst.pow 2).add (continuous_snd.pow 2))

private theorem isCompact_disk (ρ : ℝ) :
    IsCompact (disk ρ) := by
  have hbox :
      IsCompact
        (Set.Icc (-|ρ|) |ρ| ×ˢ Set.Icc (-|ρ|) |ρ|) :=
    isCompact_Icc.prod isCompact_Icc
  apply hbox.of_isClosed_subset (isClosed_disk ρ)
  intro p hp
  have hx2 : p.1 ^ 2 ≤ ρ ^ 2 := by
    dsimp [disk] at hp
    nlinarith [sq_nonneg p.2]
  have hy2 : p.2 ^ 2 ≤ ρ ^ 2 := by
    dsimp [disk] at hp
    nlinarith [sq_nonneg p.1]
  have hx2' : p.1 ^ 2 ≤ |ρ| ^ 2 := by
    simpa [sq_abs] using hx2
  have hy2' : p.2 ^ 2 ≤ |ρ| ^ 2 := by
    simpa [sq_abs] using hy2
  exact
    ⟨abs_le.mp (abs_le_of_sq_le_sq hx2' (abs_nonneg ρ)),
      abs_le.mp (abs_le_of_sq_le_sq hy2' (abs_nonneg ρ))⟩

private theorem convex_disk (ρ : ℝ) :
    Convex ℝ (disk ρ) := by
  intro p hp q hq a b ha hb hab
  change
    (a * p.1 + b * q.1) ^ 2 + (a * p.2 + b * q.2) ^ 2 ≤ ρ ^ 2
  change p.1 ^ 2 + p.2 ^ 2 ≤ ρ ^ 2 at hp
  change q.1 ^ 2 + q.2 ^ 2 ≤ ρ ^ 2 at hq
  have hx :
      (a * p.1 + b * q.1) ^ 2 ≤
        a * p.1 ^ 2 + b * q.1 ^ 2 := by
    calc
      (a * p.1 + b * q.1) ^ 2 =
          (a + b) * (a * p.1 ^ 2 + b * q.1 ^ 2) -
            a * b * (p.1 - q.1) ^ 2 := by ring
      _ = a * p.1 ^ 2 + b * q.1 ^ 2 -
            a * b * (p.1 - q.1) ^ 2 := by rw [hab, one_mul]
      _ ≤ a * p.1 ^ 2 + b * q.1 ^ 2 :=
        sub_le_self _ (mul_nonneg (mul_nonneg ha hb) (sq_nonneg _))
  have hy :
      (a * p.2 + b * q.2) ^ 2 ≤
        a * p.2 ^ 2 + b * q.2 ^ 2 := by
    calc
      (a * p.2 + b * q.2) ^ 2 =
          (a + b) * (a * p.2 ^ 2 + b * q.2 ^ 2) -
            a * b * (p.2 - q.2) ^ 2 := by ring
      _ = a * p.2 ^ 2 + b * q.2 ^ 2 -
            a * b * (p.2 - q.2) ^ 2 := by rw [hab, one_mul]
      _ ≤ a * p.2 ^ 2 + b * q.2 ^ 2 :=
        sub_le_self _ (mul_nonneg (mul_nonneg ha hb) (sq_nonneg _))
  calc
    (a * p.1 + b * q.1) ^ 2 + (a * p.2 + b * q.2) ^ 2 ≤
        a * (p.1 ^ 2 + p.2 ^ 2) +
          b * (q.1 ^ 2 + q.2 ^ 2) := by
      nlinarith
    _ ≤ a * ρ ^ 2 + b * ρ ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hp ha)
        (mul_le_mul_of_nonneg_left hq hb)
    _ = ρ ^ 2 := by rw [← add_mul, hab, one_mul]

private theorem isConnected_disk (ρ : ℝ) :
    IsConnected (disk ρ) := by
  constructor
  · refine ⟨(0, 0), ?_⟩
    simpa [disk] using sq_nonneg ρ
  · exact (convex_disk ρ).isPreconnected

private theorem complex_preimage_disk (ρ : ℝ) (hρ : 0 ≤ ρ) :
    Complex.measurableEquivRealProd ⁻¹' disk ρ =
      Metric.closedBall (0 : ℂ) ρ := by
  ext z
  simp only [Set.mem_preimage, disk, Set.mem_setOf_eq,
    Complex.measurableEquivRealProd_apply, Metric.mem_closedBall,
    dist_zero_right]
  have hzsq : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, pow_two]
  rw [hzsq]
  constructor
  · intro h
    exact (sq_le_sq₀ (norm_nonneg z) hρ).mp h
  · intro h
    exact (sq_le_sq₀ (norm_nonneg z) hρ).mpr h

private theorem volume_disk_nonneg (ρ : ℝ) (hρ : 0 ≤ ρ) :
    volume (disk ρ) = ENNReal.ofReal (Real.pi * ρ ^ 2) := by
  have hmap := Complex.volume_preserving_equiv_real_prod.map_eq
  calc
    volume (disk ρ) =
        Measure.map Complex.measurableEquivRealProd
          (volume : Measure ℂ) (disk ρ) := by rw [hmap]
    _ = volume (Complex.measurableEquivRealProd ⁻¹' disk ρ) := by
      rw [Measure.map_apply Complex.measurableEquivRealProd.measurable
        (measurableSet_disk ρ)]
    _ = volume (Metric.closedBall (0 : ℂ) ρ) := by
      rw [complex_preimage_disk ρ hρ]
    _ = ENNReal.ofReal ρ ^ 2 * NNReal.pi := by
      exact Complex.volume_closedBall 0 ρ
    _ = ENNReal.ofReal (Real.pi * ρ ^ 2) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ Real.pi)]
      rw [ENNReal.ofReal_pow hρ]
      rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
      exact mul_comm _ _

private theorem disk_abs (ρ : ℝ) :
    disk |ρ| = disk ρ := by
  ext p
  simp only [disk, Set.mem_setOf_eq, sq_abs]

private theorem volume_disk (ρ : ℝ) :
    volume (disk ρ) = ENNReal.ofReal (Real.pi * ρ ^ 2) := by
  rw [← disk_abs ρ, volume_disk_nonneg |ρ| (abs_nonneg ρ)]
  simp only [sq_abs]

private theorem volumeReal_disk (ρ : ℝ) :
    (volume (disk ρ)).toReal = Real.pi * ρ ^ 2 := by
  rw [volume_disk ρ, ENNReal.toReal_ofReal]
  positivity

private theorem integral_one_disk (ρ : ℝ) :
    (∫ _p in disk ρ, (1 : ℝ)) = Real.pi * ρ ^ 2 := by
  rw [setIntegral_const]
  simp [measureReal_def, volumeReal_disk, smul_eq_mul]

private theorem exists_isMeanPoint
    (f : (ℝ × ℝ) → ℝ) (hf : Continuous f) (ρ : ℝ) :
    ∃ p, IsMeanPoint f ρ p := by
  have hone :
      IntegrableOn (fun _p : ℝ × ℝ => (1 : ℝ)) (disk ρ) :=
    continuousOn_const.integrableOn_compact (isCompact_disk ρ)
  have hfint : IntegrableOn f (disk ρ) :=
    hf.continuousOn.integrableOn_compact (isCompact_disk ρ)
  have hfmul :
      IntegrableOn (fun p : ℝ × ℝ => f p * 1) (disk ρ) := by
    simpa only [mul_one] using hfint
  obtain ⟨p, hp, heq⟩ :=
    exists_eq_const_mul_setIntegral_of_nonneg
      (isConnected_disk ρ) (measurableSet_disk ρ) hf.continuousOn
      hone hfmul (by
        intro q hq
        norm_num)
  refine ⟨p, hp, ?_⟩
  change diskIntegral f ρ = Real.pi * ρ ^ 2 * f p
  calc
    diskIntegral f ρ =
        f p * (∫ _q in disk ρ, (1 : ℝ)) := by
      simpa [diskIntegral] using heq
    _ = Real.pi * ρ ^ 2 * f p := by
      rw [integral_one_disk]
      ring

private theorem meanPoint_spec
    (f : (ℝ × ℝ) → ℝ) (hf : Continuous f) (ρ : ℝ) :
    IsMeanPoint f ρ (meanPoint f ρ) := by
  have hex : ∃ p, IsMeanPoint f ρ p :=
    exists_isMeanPoint f hf ρ
  simpa [meanPoint, hex] using Classical.choose_spec hex

private theorem disk_mem_dist_zero_le
    {ρ : ℝ} (hρ : 0 ≤ ρ) {p : ℝ × ℝ} (hp : p ∈ disk ρ) :
    dist p (0, 0) ≤ ρ := by
  have hx2 : p.1 ^ 2 ≤ ρ ^ 2 := by
    dsimp [disk] at hp
    nlinarith [sq_nonneg p.2]
  have hy2 : p.2 ^ 2 ≤ ρ ^ 2 := by
    dsimp [disk] at hp
    nlinarith [sq_nonneg p.1]
  have hx : |p.1| ≤ ρ := abs_le_of_sq_le_sq hx2 hρ
  have hy : |p.2| ≤ ρ := abs_le_of_sq_le_sq hy2 hρ
  simpa [Prod.dist_eq, Real.dist_eq] using max_le hx hy

theorem gap1 (f : (ℝ × ℝ) → ℝ) (hf : Continuous f) (ρ : ℝ) :
    diskIntegral f ρ =
      f (meanPoint f ρ) * ∫ p in disk ρ, (1 : ℝ) := by
  have hs := (meanPoint_spec f hf ρ).2
  rw [integral_one_disk]
  calc
    diskIntegral f ρ =
        Real.pi * ρ ^ 2 * f (meanPoint f ρ) := hs
    _ = f (meanPoint f ρ) * (Real.pi * ρ ^ 2) := by ring

theorem gap2 (f : (ℝ × ℝ) → ℝ) (hf : Continuous f) (ρ : ℝ) :
    f (meanPoint f ρ) * (∫ p in disk ρ, (1 : ℝ)) =
      Real.pi * ρ ^ 2 * f (meanPoint f ρ) := by
  rw [integral_one_disk]
  ring

theorem gap3 (f : (ℝ × ℝ) → ℝ) (hf : Continuous f) (ρ : ℝ) :
    diskIntegral f ρ =
      Real.pi * ρ ^ 2 * f (meanPoint f ρ) := by
  exact (gap1 f hf ρ).trans (gap2 f hf ρ)

theorem gap4 (f : (ℝ × ℝ) → ℝ) (hf : Continuous f) (ρ : ℝ) :
    meanPoint f ρ ∈ disk ρ := by
  exact (meanPoint_spec f hf ρ).1

theorem gap5 (f : (ℝ × ℝ) → ℝ) (hf : Continuous f) :
    Tendsto (meanPoint f) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0, 0)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards
    [self_mem_nhdsWithin,
      (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds]
    with ρ hρ hρε
  exact
    (disk_mem_dist_zero_le hρ.le (gap4 f hf ρ)).trans_lt hρε

theorem gap6 (f : (ℝ × ℝ) → ℝ) (hf : Continuous f) (L : ℝ) :
    Tendsto (diskAverage f) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ↔
      Tendsto (fun ρ => f (meanPoint f ρ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  have heq :
      diskAverage f =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        fun ρ => f (meanPoint f ρ) := by
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    have hρpos : 0 < ρ := hρ
    have hρ0 : ρ ≠ 0 := hρpos.ne'
    have hden : Real.pi * ρ ^ 2 ≠ 0 :=
      mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 hρ0)
    unfold diskAverage
    rw [gap3 f hf ρ]
    field_simp [hden, hρ0]
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

theorem gap7 (f : (ℝ × ℝ) → ℝ) (hf : Continuous f) :
    Tendsto (fun ρ => f (meanPoint f ρ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f (0, 0))) := by
  exact hf.continuousAt.tendsto.comp (gap5 f hf)

theorem gap8 (f : (ℝ × ℝ) → ℝ) (hf : Continuous f) :
    Tendsto (diskAverage f)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f (0, 0))) := by
  exact (gap6 f hf (f (0, 0))).2 (gap7 f hf)

end

end ProofGap.Exercise3978
