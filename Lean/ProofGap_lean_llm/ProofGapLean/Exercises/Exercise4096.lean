import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.MeanValue
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace ProofGap.Exercise4096

noncomputable section

open MeasureTheory

def ball (R : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ R ^ 2}

def centerNorm (a b c : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2)

def distanceTo (a b c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  Real.sqrt
    ((p.1 - a) ^ 2 + (p.2.1 - b) ^ 2 + (p.2.2 - c) ^ 2)

def potential (a b c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  1 / distanceTo a b c p

def potentialIntegral (R a b c : ℝ) : ℝ :=
  ∫ p in ball R, potential a b c p

def ballVolume (R : ℝ) : ℝ :=
  4 * Real.pi / 3 * R ^ 3

def IsMeanValuePoint (R a b c : ℝ) (p : ℝ × ℝ × ℝ) : Prop :=
  p ∈ ball R ∧
    potentialIntegral R a b c = potential a b c p * ballVolume R

def distanceValues (R a b c : ℝ) : Set ℝ :=
  distanceTo a b c '' ball R

def potentialValues (R a b c : ℝ) : Set ℝ :=
  potential a b c '' ball R

def maxGap (R a b c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  1 / (centerNorm a b c - R) - potential a b c p

private abbrev Point3 := ℝ × ℝ × ℝ
private abbrev PlainPoint3 := Fin 3 → ℝ

private def unpack (p : Point3) : PlainPoint3 :=
  ![p.1, p.2.1, p.2.2]

private def euclid (p : Point3) :
    EuclideanSpace ℝ (Fin 3) :=
  @WithLp.toLp 2 PlainPoint3 (unpack p)

private def euclidLinear :
    Point3 →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun := euclid
  map_add' p q := by
    ext i
    fin_cases i <;> rfl
  map_smul' t p := by
    ext i
    fin_cases i <;> rfl

private def pack : PlainPoint3 ≃ᵐ Point3 :=
  (MeasurableEquiv.piFinSuccAbove
      (fun _i : Fin 3 => ℝ) (0 : Fin 3)).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.piFinTwo
        (fun _i : Fin 2 => ℝ)))

@[simp] private theorem pack_apply (p : PlainPoint3) :
    pack p = (p 0, p 1, p 2) := by
  rfl

private theorem pack_measurePreserving :
    MeasurePreserving pack volume volume := by
  have h₁ :
      MeasurePreserving
        (MeasurableEquiv.piFinSuccAbove
          (fun _i : Fin 3 => ℝ) (0 : Fin 3))
        volume volume :=
    volume_preserving_piFinSuccAbove
      (fun _i : Fin 3 => ℝ) (0 : Fin 3)
  have h₂ :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl ℝ)
          (MeasurableEquiv.piFinTwo
            (fun _i : Fin 2 => ℝ)))
        volume volume := by
    exact
      (MeasurePreserving.id
        (volume : Measure ℝ)).prod
          (volume_preserving_piFinTwo
            (fun _i : Fin 2 => ℝ))
  exact h₂.comp h₁

private def plainBall (R : ℝ) : Set PlainPoint3 :=
  {q | ∑ i, q i ^ 2 ≤ R ^ 2}

private theorem plainBall_eq_preimage_closedBall
    (R : ℝ) (hR : 0 ≤ R) :
    plainBall R =
      (@WithLp.toLp 2 PlainPoint3) ⁻¹'
        Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin 3)) R := by
  ext q
  simp only [plainBall, Set.mem_setOf_eq,
    Set.mem_preimage, Metric.mem_closedBall,
    dist_zero_right]
  rw [← sq_le_sq₀
    (norm_nonneg
      (@WithLp.toLp 2 PlainPoint3 q)) hR]
  rw [EuclideanSpace.real_norm_sq_eq]

private theorem pack_preimage_ball (R : ℝ) :
    pack ⁻¹' ball R = plainBall R := by
  ext q
  simp [ball, plainBall, Fin.sum_univ_succ]
  ring_nf

private theorem ball_measurable (R : ℝ) :
    MeasurableSet (ball R) := by
  unfold ball
  exact measurableSet_le (by fun_prop) (by fun_prop)

private theorem ball_volumeReal
    (R : ℝ) (hR : 0 ≤ R) :
    (volume (ball R)).toReal = ballVolume R := by
  rw [← pack_measurePreserving.measure_preimage
    (ball_measurable R).nullMeasurableSet]
  rw [pack_preimage_ball R,
    plainBall_eq_preimage_closedBall R hR]
  rw [(PiLp.volume_preserving_toLp
    (Fin 3)).measure_preimage
      measurableSet_closedBall.nullMeasurableSet]
  rw [EuclideanSpace.volume_closedBall_fin_three]
  have hconst : 0 ≤ Real.pi * 4 / 3 := by
    positivity
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hR,
    ENNReal.toReal_ofReal hconst]
  unfold ballVolume
  ring

private def centerPoint (a b c : ℝ) : Point3 :=
  (a, b, c)

private theorem centerNorm_eq_norm (a b c : ℝ) :
    centerNorm a b c =
      ‖euclid (centerPoint a b c)‖ := by
  calc
    centerNorm a b c =
        Real.sqrt
          (‖euclid (centerPoint a b c)‖ ^ 2) := by
      unfold centerNorm
      rw [show
        ‖euclid (centerPoint a b c)‖ ^ 2 =
          a ^ 2 + b ^ 2 + c ^ 2 by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [euclid, unpack, centerPoint,
          Fin.sum_univ_succ]
        ring]
    _ = ‖euclid (centerPoint a b c)‖ := by
      exact Real.sqrt_sq (norm_nonneg _)

private theorem distanceTo_eq_norm
    (a b c : ℝ) (p : Point3) :
    distanceTo a b c p =
      ‖euclid p - euclid (centerPoint a b c)‖ := by
  rw [show
    euclid p - euclid (centerPoint a b c) =
      euclid (p - centerPoint a b c) by
      ext i
      fin_cases i <;> rfl]
  calc
    distanceTo a b c p =
        Real.sqrt
          (‖euclid
            (p - centerPoint a b c)‖ ^ 2) := by
      unfold distanceTo
      congr 1
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [euclid, unpack, centerPoint,
        Fin.sum_univ_succ]
      ring
    _ = ‖euclid
          (p - centerPoint a b c)‖ := by
      exact Real.sqrt_sq (norm_nonneg _)

private theorem mem_ball_iff_norm
    (R : ℝ) (hR : 0 ≤ R) (p : Point3) :
    p ∈ ball R ↔ ‖euclid p‖ ≤ R := by
  unfold ball
  change
    (p.1 ^ 2 + p.2.1 ^ 2 +
      p.2.2 ^ 2 ≤ R ^ 2) ↔
      ‖euclid p‖ ≤ R
  rw [← show
    ‖euclid p‖ ^ 2 =
      p.1 ^ 2 + p.2.1 ^ 2 +
        p.2.2 ^ 2 by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [euclid, unpack, Fin.sum_univ_succ]
    ring]
  exact sq_le_sq₀ (norm_nonneg _) hR

private theorem distance_bounds
    (R a b c : ℝ) (hR : 0 ≤ R)
    (p : Point3) (hp : p ∈ ball R) :
    centerNorm a b c - R ≤
        distanceTo a b c p ∧
      distanceTo a b c p ≤
        centerNorm a b c + R := by
  have hpnorm : ‖euclid p‖ ≤ R :=
    (mem_ball_iff_norm R hR p).1 hp
  rw [centerNorm_eq_norm, distanceTo_eq_norm]
  constructor
  · calc
      ‖euclid (centerPoint a b c)‖ - R ≤
          ‖euclid (centerPoint a b c)‖ -
            ‖euclid p‖ := by
        linarith
      _ ≤ ‖euclid (centerPoint a b c) -
            euclid p‖ :=
        norm_sub_norm_le _ _
      _ = ‖euclid p -
            euclid (centerPoint a b c)‖ :=
        norm_sub_rev _ _
  · calc
      ‖euclid p -
          euclid (centerPoint a b c)‖ ≤
          ‖euclid p‖ +
            ‖euclid (centerPoint a b c)‖ :=
        norm_sub_le _ _
      _ ≤ ‖euclid (centerPoint a b c)‖ + R := by
        linarith

private def nearPoint (R a b c : ℝ) : Point3 :=
  (R / centerNorm a b c) • centerPoint a b c

private def farPoint (R a b c : ℝ) : Point3 :=
  (-R / centerNorm a b c) • centerPoint a b c

private theorem euclid_smul
    (t : ℝ) (p : Point3) :
    euclid (t • p) = t • euclid p := by
  ext i
  fin_cases i <;> rfl

private theorem nearPoint_norm
    (R a b c : ℝ) (hR : 0 ≤ R)
    (hout : R < centerNorm a b c) :
    ‖euclid (nearPoint R a b c)‖ = R := by
  have hN : 0 < centerNorm a b c :=
    hR.trans_lt hout
  rw [nearPoint, euclid_smul, norm_smul,
    Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hR hN.le),
    ← centerNorm_eq_norm]
  field_simp

private theorem farPoint_norm
    (R a b c : ℝ) (hR : 0 ≤ R)
    (hout : R < centerNorm a b c) :
    ‖euclid (farPoint R a b c)‖ = R := by
  have hN : 0 < centerNorm a b c :=
    hR.trans_lt hout
  rw [farPoint, euclid_smul, norm_smul,
    Real.norm_eq_abs,
    show |-R / centerNorm a b c| =
      R / centerNorm a b c by
      rw [abs_div, abs_neg, abs_of_nonneg hR,
        abs_of_pos hN],
    ← centerNorm_eq_norm]
  field_simp

private theorem nearPoint_distance
    (R a b c : ℝ) (hR : 0 ≤ R)
    (hout : R < centerNorm a b c) :
    distanceTo a b c (nearPoint R a b c) =
      centerNorm a b c - R := by
  have hN : 0 < centerNorm a b c :=
    hR.trans_lt hout
  rw [distanceTo_eq_norm, nearPoint, euclid_smul,
    show
      (R / centerNorm a b c) •
          euclid (centerPoint a b c) -
          euclid (centerPoint a b c) =
        (R / centerNorm a b c - 1) •
          euclid (centerPoint a b c) by
      module,
    norm_smul, Real.norm_eq_abs,
    abs_of_neg
      (sub_neg.mpr ((div_lt_one hN).2 hout)),
    ← centerNorm_eq_norm]
  field_simp
  ring

private theorem farPoint_distance
    (R a b c : ℝ) (hR : 0 ≤ R)
    (hout : R < centerNorm a b c) :
    distanceTo a b c (farPoint R a b c) =
      centerNorm a b c + R := by
  have hN : 0 < centerNorm a b c :=
    hR.trans_lt hout
  rw [distanceTo_eq_norm, farPoint, euclid_smul,
    show
      (-R / centerNorm a b c) •
          euclid (centerPoint a b c) -
          euclid (centerPoint a b c) =
        (-R / centerNorm a b c - 1) •
          euclid (centerPoint a b c) by
      module,
    norm_smul, Real.norm_eq_abs,
    abs_of_neg (by
      have hnonpos :
          -R / centerNorm a b c ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr hR) hN.le
      linarith),
    ← centerNorm_eq_norm]
  field_simp
  ring

private theorem nearPoint_mem
    (R a b c : ℝ) (hR : 0 ≤ R)
    (hout : R < centerNorm a b c) :
    nearPoint R a b c ∈ ball R := by
  rw [mem_ball_iff_norm R hR,
    nearPoint_norm R a b c hR hout]

private theorem farPoint_mem
    (R a b c : ℝ) (hR : 0 ≤ R)
    (hout : R < centerNorm a b c) :
    farPoint R a b c ∈ ball R := by
  rw [mem_ball_iff_norm R hR,
    farPoint_norm R a b c hR hout]

private theorem ball_eq_preimage_closedBall
    (R : ℝ) (hR : 0 ≤ R) :
    ball R =
      euclid ⁻¹'
        Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin 3)) R := by
  ext p
  simp only [Set.mem_preimage,
    Metric.mem_closedBall, dist_zero_right]
  exact mem_ball_iff_norm R hR p

private theorem ball_isClosed
    (R : ℝ) (hR : 0 ≤ R) :
    IsClosed (ball R) := by
  rw [ball_eq_preimage_closedBall R hR]
  exact Metric.isClosed_closedBall.preimage
    euclidLinear.continuous_of_finiteDimensional

private theorem ball_norm_le
    (R : ℝ) (hR : 0 ≤ R) (p : Point3)
    (hp : p ∈ ball R) :
    ‖p‖ ≤ R := by
  have hp' :=
    (mem_ball_iff_norm R hR p).1 hp
  have h0 :=
    PiLp.norm_apply_le (euclid p) (0 : Fin 3)
  have h1 :=
    PiLp.norm_apply_le (euclid p) (1 : Fin 3)
  have h2 :=
    PiLp.norm_apply_le (euclid p) (2 : Fin 3)
  simp only [Prod.norm_def, Real.norm_eq_abs]
  apply max_le
  · simpa [euclid, unpack] using h0.trans hp'
  · apply max_le
    · simpa [euclid, unpack] using h1.trans hp'
    · simpa [euclid, unpack] using h2.trans hp'

private theorem ball_isBounded
    (R : ℝ) (hR : 0 ≤ R) :
    Bornology.IsBounded (ball R) := by
  refine
    (Metric.isBounded_iff_subset_closedBall
      (0 : Point3)).2 ⟨R, ?_⟩
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right]
  exact ball_norm_le R hR p hp

private theorem ball_isCompact
    (R : ℝ) (hR : 0 ≤ R) :
    IsCompact (ball R) :=
  Metric.isCompact_iff_isClosed_bounded.2
    ⟨ball_isClosed R hR, ball_isBounded R hR⟩

private theorem ball_convex
    (R : ℝ) (hR : 0 ≤ R) :
    Convex ℝ (ball R) := by
  rw [ball_eq_preimage_closedBall R hR]
  exact Convex.linear_preimage
    (convex_closedBall
      (0 : EuclideanSpace ℝ (Fin 3)) R)
    euclidLinear

private theorem ball_connected
    (R : ℝ) (hR : 0 ≤ R) :
    IsConnected (ball R) := by
  apply (ball_convex R hR).isConnected
  refine ⟨0, ?_⟩
  rw [mem_ball_iff_norm R hR]
  have hz :
      euclid (0 : Point3) =
        (0 : EuclideanSpace ℝ (Fin 3)) := by
    ext i
    fin_cases i <;> rfl
  rw [hz, norm_zero]
  exact hR

private theorem ball_interior_nonempty
    (R : ℝ) (hR : 0 < R) :
    (interior (ball R)).Nonempty := by
  refine ⟨0, mem_interior.2 ?_⟩
  let U : Set Point3 :=
    {p |
      p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 <
        R ^ 2}
  refine ⟨U, ?_, ?_, ?_⟩
  · intro p hp
    change
      p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤
        R ^ 2
    exact hp.le
  · dsimp [U]
    exact isOpen_lt (by fun_prop) (by fun_prop)
  · dsimp [U]
    simpa using (sq_pos_of_pos hR)

private theorem ball_subset_closure_interior
    (R : ℝ) (hR : 0 < R) :
    ball R ⊆ closure (interior (ball R)) := by
  have hclosure :=
    Convex.closure_interior_eq_closure_of_nonempty_interior
      (ball_convex R hR.le)
      (ball_interior_nonempty R hR)
  rw [hclosure, (ball_isClosed R hR.le).closure_eq]

private theorem distanceTo_continuous (a b c : ℝ) :
    Continuous (distanceTo a b c) := by
  unfold distanceTo
  fun_prop

private theorem distanceTo_pos_on_ball
    (R a b c : ℝ) (hR : 0 < R)
    (hout : R < centerNorm a b c)
    (p : Point3) (hp : p ∈ ball R) :
    0 < distanceTo a b c p := by
  have hb :=
    (distance_bounds R a b c hR.le p hp).1
  linarith

private theorem potential_continuousOn
    (R a b c : ℝ) (hR : 0 < R)
    (hout : R < centerNorm a b c) :
    ContinuousOn (potential a b c) (ball R) := by
  unfold potential
  simpa [one_div] using
    (distanceTo_continuous a b c).continuousOn.inv₀
      (fun p hp =>
        (distanceTo_pos_on_ball
          R a b c hR hout p hp).ne')

private theorem potential_integrableOn
    (R a b c : ℝ) (hR : 0 < R)
    (hout : R < centerNorm a b c) :
    IntegrableOn (potential a b c)
      (ball R) volume :=
  (potential_continuousOn
    R a b c hR hout).integrableOn_compact
      (ball_isCompact R hR.le)

private theorem eq_zero_on_ball_of_integral_eq_zero
    (R : ℝ) (hR : 0 < R)
    (f : Point3 → ℝ)
    (hfcont : ContinuousOn f (ball R))
    (hfnonneg : ∀ p ∈ ball R, 0 ≤ f p)
    (hfint : IntegrableOn f (ball R) volume)
    (hzero : (∫ p in ball R, f p) = 0) :
    ∀ p ∈ ball R, f p = 0 := by
  have hnonnegAe :
      0 ≤ᵐ[volume.restrict (ball R)] f := by
    filter_upwards
      [ae_restrict_mem (ball_measurable R)]
        with p hp
    exact hfnonneg p hp
  have hae :
      f =ᵐ[volume.restrict (ball R)] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae
      hnonnegAe hfint).1 hzero
  exact MeasureTheory.Measure.eqOn_of_ae_eq
    hae hfcont continuousOn_const
    (ball_subset_closure_interior R hR)

private def minGap
    (R a b c : ℝ) (p : Point3) : ℝ :=
  potential a b c p -
    1 / (centerNorm a b c + R)

private theorem reciprocal_gap_pos
    (R a b c : ℝ) (hR : 0 < R)
    (hout : R < centerNorm a b c) :
    1 / (centerNorm a b c + R) <
      1 / (centerNorm a b c - R) := by
  apply one_div_lt_one_div_of_lt
  · linarith
  · linarith

private theorem mean_potential_ne_min
    (R a b c : ℝ) (p : Point3)
    (hR : 0 < R)
    (hout : R < centerNorm a b c)
    (hp : IsMeanValuePoint R a b c p) :
    potential a b c p ≠
      1 / (centerNorm a b c + R) := by
  intro hmin
  have hcont :
      ContinuousOn (minGap R a b c)
        (ball R) := by
    unfold minGap
    exact
      (potential_continuousOn
        R a b c hR hout).sub continuousOn_const
  have hnonneg :
      ∀ q ∈ ball R, 0 ≤ minGap R a b c q := by
    intro q hq
    unfold minGap potential
    have hdist :
        0 < distanceTo a b c q :=
      distanceTo_pos_on_ball
        R a b c hR hout q hq
    exact sub_nonneg.mpr
      (one_div_le_one_div_of_le hdist
        (distance_bounds
          R a b c hR.le q hq).2)
  have hint :
      IntegrableOn (minGap R a b c)
        (ball R) volume :=
    hcont.integrableOn_compact
      (ball_isCompact R hR.le)
  have hzero :
      (∫ q in ball R, minGap R a b c q) = 0 := by
    have hconst :
        IntegrableOn
          (fun _ : Point3 =>
            1 / (centerNorm a b c + R))
          (ball R) volume :=
      continuousOn_const.integrableOn_compact
        (ball_isCompact R hR.le)
    have hpot :=
      potential_integrableOn R a b c hR hout
    unfold minGap
    rw [integral_sub hpot hconst]
    rw [setIntegral_const, smul_eq_mul,
      measureReal_def, ball_volumeReal R hR.le]
    unfold ballVolume
    unfold IsMeanValuePoint at hp
    unfold potentialIntegral at hp
    unfold ballVolume at hp
    rw [hp.2, hmin]
    ring
  have hall :=
    eq_zero_on_ball_of_integral_eq_zero
      R hR (minGap R a b c)
      hcont hnonneg hint hzero
  have hz :=
    hall (nearPoint R a b c)
      (nearPoint_mem R a b c hR.le hout)
  unfold minGap potential at hz
  rw [nearPoint_distance
    R a b c hR.le hout] at hz
  linarith [reciprocal_gap_pos
    R a b c hR hout]

theorem gap1 (R a b c : ℝ) (hR : 0 < R)
    (hout : R < centerNorm a b c) :
    ∃ p, IsMeanValuePoint R a b c p := by
  have hcompact := ball_isCompact R hR.le
  have hpot :=
    potential_continuousOn R a b c hR hout
  have hpotInt :
      IntegrableOn (potential a b c)
        (ball R) volume :=
    hpot.integrableOn_compact hcompact
  have honeInt :
      IntegrableOn
        (fun _ : Point3 => (1 : ℝ))
        (ball R) volume :=
    continuousOn_const.integrableOn_compact hcompact
  obtain ⟨p, hp, hmean⟩ :=
    exists_eq_const_mul_setIntegral_of_nonneg
      (ball_connected R hR.le)
      (ball_measurable R)
      hpot honeInt (by simpa using hpotInt)
      (by intro q hq; positivity)
  refine ⟨p, hp, ?_⟩
  unfold potentialIntegral
  have hvol :
      (volume (ball R)).toReal = ballVolume R :=
    ball_volumeReal R hR.le
  simpa [measureReal_def, hvol] using hmean

theorem gap2 (R a b c : ℝ) (p : ℝ × ℝ × ℝ)
    (hp : IsMeanValuePoint R a b c p) :
    p ∈ ball R := by
  exact hp.1

theorem gap3 (R a b c : ℝ) (hR : 0 < R)
    (hout : R < centerNorm a b c) :
    IsLeast (distanceValues R a b c)
      (centerNorm a b c - R) := by
  constructor
  · refine ⟨nearPoint R a b c,
      nearPoint_mem R a b c hR.le hout, ?_⟩
    exact nearPoint_distance R a b c hR.le hout
  · rintro d ⟨q, hq, rfl⟩
    exact (distance_bounds R a b c hR.le q hq).1

theorem gap4 (R a b c : ℝ) (hR : 0 < R)
    (hout : R < centerNorm a b c) :
    IsGreatest (distanceValues R a b c)
      (centerNorm a b c + R) := by
  constructor
  · refine ⟨farPoint R a b c,
      farPoint_mem R a b c hR.le hout, ?_⟩
    exact farPoint_distance R a b c hR.le hout
  · rintro d ⟨q, hq, rfl⟩
    exact (distance_bounds R a b c hR.le q hq).2

theorem gap5 (R a b c : ℝ) (hR : 0 < R)
    (hout : R < centerNorm a b c) :
    IsGreatest (potentialValues R a b c)
      (1 / (centerNorm a b c - R)) := by
  have hlow :
      0 < centerNorm a b c - R := by
    linarith
  constructor
  · refine ⟨nearPoint R a b c,
      nearPoint_mem R a b c hR.le hout, ?_⟩
    unfold potential
    rw [nearPoint_distance R a b c hR.le hout]
  · rintro v ⟨q, hq, rfl⟩
    unfold potential
    exact one_div_le_one_div_of_le hlow
      (distance_bounds R a b c hR.le q hq).1

theorem gap6 (R a b c : ℝ) (hR : 0 < R)
    (hout : R < centerNorm a b c) :
    IsLeast (potentialValues R a b c)
      (1 / (centerNorm a b c + R)) := by
  constructor
  · refine ⟨farPoint R a b c,
      farPoint_mem R a b c hR.le hout, ?_⟩
    unfold potential
    rw [farPoint_distance R a b c hR.le hout]
  · rintro v ⟨q, hq, rfl⟩
    unfold potential
    have hdist :
        0 < distanceTo a b c q :=
      distanceTo_pos_on_ball
        R a b c hR hout q hq
    exact one_div_le_one_div_of_le hdist
      (distance_bounds R a b c hR.le q hq).2

theorem gap7 (R a b c : ℝ) (p : ℝ × ℝ × ℝ)
    (hR : 0 < R) (hout : R < centerNorm a b c)
    (hp : IsMeanValuePoint R a b c p)
    (hmax : potential a b c p = 1 / (centerNorm a b c - R)) :
    (∫ q in ball R, maxGap R a b c q) = 0 := by
  have hconst :
      IntegrableOn
        (fun _ : Point3 =>
          1 / (centerNorm a b c - R))
        (ball R) volume :=
    continuousOn_const.integrableOn_compact
      (ball_isCompact R hR.le)
  have hpot :=
    potential_integrableOn R a b c hR hout
  unfold maxGap
  rw [integral_sub hconst hpot]
  rw [setIntegral_const, smul_eq_mul,
    measureReal_def, ball_volumeReal R hR.le]
  unfold IsMeanValuePoint at hp
  unfold potentialIntegral at hp
  rw [hp.2, hmax]
  ring

theorem gap8 (R a b c : ℝ) (hR : 0 < R)
    (hout : R < centerNorm a b c) :
    ∀ q ∈ ball R, 0 ≤ maxGap R a b c q := by
  intro q hq
  unfold maxGap potential
  have hb :=
    (distance_bounds R a b c hR.le q hq).1
  have hlow :
      0 < centerNorm a b c - R := by
    linarith
  exact sub_nonneg.mpr
    (one_div_le_one_div_of_le hlow hb)

theorem gap9 (R a b c : ℝ) (hR : 0 < R)
    (hout : R < centerNorm a b c) :
    ContinuousOn (maxGap R a b c) (ball R) := by
  unfold maxGap
  exact continuousOn_const.sub
    (potential_continuousOn R a b c hR hout)

theorem gap10 (R a b c : ℝ) (p : ℝ × ℝ × ℝ)
    (hR : 0 < R) (hout : R < centerNorm a b c)
    (hp : IsMeanValuePoint R a b c p)
    (hmax : potential a b c p = 1 / (centerNorm a b c - R)) :
    ∀ q ∈ ball R, maxGap R a b c q = 0 := by
  apply eq_zero_on_ball_of_integral_eq_zero
    R hR (maxGap R a b c)
  · exact gap9 R a b c hR hout
  · exact gap8 R a b c hR hout
  · exact
      (gap9 R a b c hR hout).integrableOn_compact
        (ball_isCompact R hR.le)
  · exact gap7 R a b c p hR hout hp hmax

theorem gap11 (R a b c : ℝ) (p : ℝ × ℝ × ℝ)
    (hR : 0 < R) (hout : R < centerNorm a b c)
    (hp : IsMeanValuePoint R a b c p)
    (hmax : potential a b c p = 1 / (centerNorm a b c - R)) :
    False := by
  have hz :=
    gap10 R a b c p hR hout hp hmax
      (farPoint R a b c)
      (farPoint_mem R a b c hR.le hout)
  unfold maxGap potential at hz
  rw [farPoint_distance
    R a b c hR.le hout] at hz
  linarith [reciprocal_gap_pos
    R a b c hR hout]

theorem gap12 (R a b c : ℝ) (p : ℝ × ℝ × ℝ)
    (hR : 0 < R) (hout : R < centerNorm a b c)
    (hp : IsMeanValuePoint R a b c p) :
    1 / (centerNorm a b c + R) <
      potential a b c p := by
  have hmem : p ∈ ball R :=
    gap2 R a b c p hp
  have hle :
      1 / (centerNorm a b c + R) ≤
        potential a b c p :=
    (gap6 R a b c hR hout).2
      ⟨p, hmem, rfl⟩
  exact lt_of_le_of_ne hle
    (mean_potential_ne_min
      R a b c p hR hout hp).symm

theorem gap13 (R a b c : ℝ) (p : ℝ × ℝ × ℝ)
    (hR : 0 < R) (hout : R < centerNorm a b c)
    (hp : IsMeanValuePoint R a b c p) :
    potential a b c p <
      1 / (centerNorm a b c - R) := by
  have hmem : p ∈ ball R :=
    gap2 R a b c p hp
  have hle :
      potential a b c p ≤
        1 / (centerNorm a b c - R) :=
    (gap5 R a b c hR hout).2
      ⟨p, hmem, rfl⟩
  apply lt_of_le_of_ne hle
  intro heq
  exact gap11 R a b c p hR hout hp heq

theorem gap14 (R a b c : ℝ) (hR : 0 < R)
    (hout : R < centerNorm a b c) :
    1 / (centerNorm a b c + R) <
      1 / (centerNorm a b c - R) := by
  exact reciprocal_gap_pos R a b c hR hout

theorem gap15 (R a b c : ℝ) (p : ℝ × ℝ × ℝ)
    (hR : 0 < R) (hout : R < centerNorm a b c)
    (hp : IsMeanValuePoint R a b c p) :
    centerNorm a b c - R <
      distanceTo a b c p := by
  have hdist :
      0 < distanceTo a b c p :=
    distanceTo_pos_on_ball
      R a b c hR hout p (gap2 R a b c p hp)
  exact lt_of_one_div_lt_one_div hdist
    (gap13 R a b c p hR hout hp)

theorem gap16 (R a b c : ℝ) (p : ℝ × ℝ × ℝ)
    (hR : 0 < R) (hout : R < centerNorm a b c)
    (hp : IsMeanValuePoint R a b c p) :
    distanceTo a b c p <
      centerNorm a b c + R := by
  have hsum :
      0 < centerNorm a b c + R := by
    linarith
  exact lt_of_one_div_lt_one_div hsum
    (gap12 R a b c p hR hout hp)

theorem gap17 (R a b c : ℝ) (hR : 0 < R) :
    centerNorm a b c - R <
      centerNorm a b c + R := by
  linarith

theorem gap18 (R a b c : ℝ) (p : ℝ × ℝ × ℝ)
    (hR : 0 < R) (hout : R < centerNorm a b c)
    (hp : IsMeanValuePoint R a b c p) :
    ∃ theta, distanceTo a b c p =
        centerNorm a b c + theta * R ∧
      |theta| < 1 := by
  let theta :=
    (distanceTo a b c p - centerNorm a b c) / R
  refine ⟨theta, ?_, ?_⟩
  · dsimp [theta]
    field_simp [hR.ne']
    ring
  · dsimp [theta]
    rw [abs_lt]
    constructor
    · apply (lt_div_iff₀ hR).2
      linarith [gap15 R a b c p hR hout hp]
    · apply (div_lt_iff₀ hR).2
      linarith [gap16 R a b c p hR hout hp]

theorem gap19 (R a b c : ℝ) (p : ℝ × ℝ × ℝ)
    (hR : 0 < R) (hout : R < centerNorm a b c)
    (hp : IsMeanValuePoint R a b c p) :
    ∃ theta, |theta| < 1 ∧
      distanceTo a b c p =
        centerNorm a b c + theta * R := by
  obtain ⟨theta, hdist, htheta⟩ :=
    gap18 R a b c p hR hout hp
  exact ⟨theta, htheta, hdist⟩

theorem gap20 (R a b c : ℝ) (hR : 0 < R)
    (hout : R < centerNorm a b c) :
    ∃ theta, |theta| < 1 ∧
      potentialIntegral R a b c =
        ballVolume R /
          (centerNorm a b c + theta * R) := by
  obtain ⟨p, hp⟩ := gap1 R a b c hR hout
  obtain ⟨theta, htheta, hdist⟩ :=
    gap19 R a b c p hR hout hp
  refine ⟨theta, htheta, ?_⟩
  rw [hp.2]
  unfold potential
  rw [hdist]
  ring

end

end ProofGap.Exercise4096
