import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise4391

noncomputable section

open Filter MeasureTheory

abbrev Vec3 := ℝ × ℝ × ℝ
abbrev SurfaceIntegral := (Vec3 → ℝ) → ℝ

def distance (q p : Vec3) : ℝ :=
  Real.sqrt ((p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 +
    (p.2.2 - q.2.2) ^ 2)

def radialUnit (q p : Vec3) : Vec3 :=
  ((p.1 - q.1) / distance q p,
    (p.2.1 - q.2.1) / distance q p,
    (p.2.2 - q.2.2) / distance q p)

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def normalComponent (q p n : Vec3) : ℝ :=
  dot (radialUnit q p) n

def partialX (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => u (x, p.2.1, p.2.2)) p.1

def partialY (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => u (p.1, y, p.2.2)) p.2.1

def partialZ (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => u (p.1, p.2.1, z)) p.2.2

def divergence (a : Vec3 → Vec3) (p : Vec3) : ℝ :=
  partialX (fun x => (a x).1) p +
    partialY (fun x => (a x).2.1) p +
      partialZ (fun x => (a x).2.2) p

def radialDivergence (q p : Vec3) : ℝ :=
  divergence (radialUnit q) p

def inverseDistanceVolume (V : Set Vec3) (q : Vec3) : ℝ :=
  ∫ p in V, 1 / distance q p

def divergenceVolume (V : Set Vec3) (q : Vec3) : ℝ :=
  ∫ p in V, radialDivergence q p

def boundaryRadialFlux (I : SurfaceIntegral) (q : Vec3)
    (normal : Vec3 → Vec3) : ℝ :=
  I (fun p => normalComponent q p (normal p))

def surfaceFlux (I : SurfaceIntegral) (a normal : Vec3 → Vec3) : ℝ :=
  I (fun p => dot (a p) (normal p))

def deletedBall (q : Vec3) (ε : ℝ) : Set Vec3 :=
  {p | distance q p < ε}

def closedBall3 (q : Vec3) (ε : ℝ) : Set Vec3 :=
  {p | distance q p ≤ ε}

def puncturedPotential (V : Set Vec3) (q : Vec3) (ε : ℝ) : ℝ :=
  ∫ p in V \ deletedBall q ε, 1 / distance q p

def spherePoint (q : Vec3) (ε θ φ : ℝ) : Vec3 :=
  (q.1 + ε * Real.sin φ * Real.cos θ,
    q.2.1 + ε * Real.sin φ * Real.sin θ,
    q.2.2 + ε * Real.cos φ)

def inwardSphereAreaVector (ε θ φ : ℝ) : Vec3 :=
  (-ε ^ 2 * Real.sin φ ^ 2 * Real.cos θ,
    -ε ^ 2 * Real.sin φ ^ 2 * Real.sin θ,
    -ε ^ 2 * Real.sin φ * Real.cos φ)

def sphereFlux (a : Vec3 → Vec3) (q : Vec3) (ε : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi,
    ∫ φ in (0 : ℝ)..Real.pi,
      dot (a (spherePoint q ε θ φ)) (inwardSphereAreaVector ε θ φ)

def innerSphereFlux (q : Vec3) (ε : ℝ) : ℝ :=
  sphereFlux (radialUnit q) q ε

def SatisfiesGaussOn (V : Set Vec3) (I : SurfaceIntegral)
    (normal : Vec3 → Vec3) : Prop :=
  ∀ a : Vec3 → Vec3, (∀ p ∈ V, DifferentiableAt ℝ a p) →
    surfaceFlux I a normal = ∫ p in V, divergence a p

def SatisfiesPuncturedGauss (V : Set Vec3) (I : SurfaceIntegral)
    (normal : Vec3 → Vec3) : Prop :=
  ∀ (a : Vec3 → Vec3) (q : Vec3) (ε : ℝ), 0 < ε →
    closedBall3 q ε ⊆ interior V →
    (∀ p ∈ V \ deletedBall q ε, DifferentiableAt ℝ a p) →
    surfaceFlux I a normal + sphereFlux a q ε =
      ∫ p in V \ deletedBall q ε, divergence a p

private theorem radialRegular (q p : Vec3) (hpq : p ≠ q) :
    0 < distance q p ∧
      DifferentiableAt ℝ (radialUnit q) p ∧
      radialDivergence q p = 2 / distance q p := by
  have hc : p.1 ≠ q.1 ∨ p.2.1 ≠ q.2.1 ∨ p.2.2 ≠ q.2.2 := by
    by_contra h
    push_neg at h
    exact hpq (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
  have hspos : 0 <
      (p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 +
        (p.2.2 - q.2.2) ^ 2 := by
    rcases hc with hx | hy | hz
    · have hx' : 0 < (p.1 - q.1) ^ 2 :=
        sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
      nlinarith [sq_nonneg (p.2.1 - q.2.1),
        sq_nonneg (p.2.2 - q.2.2)]
    · have hy' : 0 < (p.2.1 - q.2.1) ^ 2 :=
        sq_pos_of_ne_zero (sub_ne_zero.mpr hy)
      nlinarith [sq_nonneg (p.1 - q.1),
        sq_nonneg (p.2.2 - q.2.2)]
    · have hz' : 0 < (p.2.2 - q.2.2) ^ 2 :=
        sq_pos_of_ne_zero (sub_ne_zero.mpr hz)
      nlinarith [sq_nonneg (p.1 - q.1),
        sq_nonneg (p.2.1 - q.2.1)]
  have hdpos : 0 < distance q p := Real.sqrt_pos.2 hspos
  have hsne :
      (p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 +
          (p.2.2 - q.2.2) ^ 2 ≠ 0 := ne_of_gt hspos
  have hdne : distance q p ≠ 0 := ne_of_gt hdpos
  have hinner : DifferentiableAt ℝ
      (fun x : Vec3 =>
        (x.1 - q.1) ^ 2 + (x.2.1 - q.2.1) ^ 2 +
          (x.2.2 - q.2.2) ^ 2) p := by
    fun_prop
  have hdist : DifferentiableAt ℝ (distance q) p := by
    unfold distance
    exact (Real.hasDerivAt_sqrt hsne).differentiableAt.comp p hinner
  have hnumX : DifferentiableAt ℝ (fun x : Vec3 => x.1 - q.1) p := by
    fun_prop
  have hnumY : DifferentiableAt ℝ (fun x : Vec3 => x.2.1 - q.2.1) p := by
    fun_prop
  have hnumZ : DifferentiableAt ℝ (fun x : Vec3 => x.2.2 - q.2.2) p := by
    fun_prop
  have hinvdist : DifferentiableAt ℝ
      (fun x : Vec3 => (distance q x)⁻¹) p := by
    have hinv : DifferentiableAt ℝ (fun r : ℝ => r⁻¹)
        (distance q p) := by
      simpa only [id_eq] using
        ((hasDerivAt_id (distance q p)).inv hdne).differentiableAt
    exact hinv.comp p hdist
  rcases hnumX with ⟨dX, hNumX⟩
  rcases hnumY with ⟨dY, hNumY⟩
  rcases hnumZ with ⟨dZ, hNumZ⟩
  rcases hinvdist with ⟨dInv, hInv⟩
  have hdiffX : DifferentiableAt ℝ
      (fun x : Vec3 => (x.1 - q.1) / distance q x) p := by
    simpa only [div_eq_mul_inv] using
      (hNumX.mul hInv).differentiableAt
  have hdiffY : DifferentiableAt ℝ
      (fun x : Vec3 => (x.2.1 - q.2.1) / distance q x) p := by
    simpa only [div_eq_mul_inv] using
      (hNumY.mul hInv).differentiableAt
  have hdiffZ : DifferentiableAt ℝ
      (fun x : Vec3 => (x.2.2 - q.2.2) / distance q x) p := by
    simpa only [div_eq_mul_inv] using
      (hNumZ.mul hInv).differentiableAt
  have hdiff : DifferentiableAt ℝ (radialUnit q) p := by
    unfold radialUnit
    fun_prop
  refine ⟨hdpos, hdiff, ?_⟩
  have hSx : HasDerivAt
      (fun x : ℝ =>
        (x - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 +
          (p.2.2 - q.2.2) ^ 2)
      (2 * (p.1 - q.1)) p.1 := by
    convert ((((hasDerivAt_id p.1).sub_const q.1).pow 2).add_const
      ((p.2.1 - q.2.1) ^ 2)).add_const
        ((p.2.2 - q.2.2) ^ 2) using 1 <;>
      simp only [id_eq] <;> ring_nf
  have hSy : HasDerivAt
      (fun y : ℝ =>
        (p.1 - q.1) ^ 2 + (y - q.2.1) ^ 2 +
          (p.2.2 - q.2.2) ^ 2)
      (2 * (p.2.1 - q.2.1)) p.2.1 := by
    convert (((((hasDerivAt_id p.2.1).sub_const q.2.1).pow 2).const_add
      ((p.1 - q.1) ^ 2)).add_const
        ((p.2.2 - q.2.2) ^ 2)) using 1 <;>
      simp only [id_eq] <;> ring_nf
  have hSz : HasDerivAt
      (fun z : ℝ =>
        (p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 +
          (z - q.2.2) ^ 2)
      (2 * (p.2.2 - q.2.2)) p.2.2 := by
    convert ((((hasDerivAt_id p.2.2).sub_const q.2.2).pow 2).const_add
      ((p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2)) using 1 <;>
      simp only [id_eq] <;> ring_nf
  have hrootX : HasDerivAt
      (fun x : ℝ => Real.sqrt
        ((x - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 +
          (p.2.2 - q.2.2) ^ 2))
      (1 / (2 * Real.sqrt
        ((p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 +
          (p.2.2 - q.2.2) ^ 2)) * (2 * (p.1 - q.1))) p.1 := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sqrt hsne).comp p.1 hSx
  have hrootY : HasDerivAt
      (fun y : ℝ => Real.sqrt
        ((p.1 - q.1) ^ 2 + (y - q.2.1) ^ 2 +
          (p.2.2 - q.2.2) ^ 2))
      (1 / (2 * Real.sqrt
        ((p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 +
          (p.2.2 - q.2.2) ^ 2)) * (2 * (p.2.1 - q.2.1))) p.2.1 := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sqrt hsne).comp p.2.1 hSy
  have hrootZ : HasDerivAt
      (fun z : ℝ => Real.sqrt
        ((p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 +
          (z - q.2.2) ^ 2))
      (1 / (2 * Real.sqrt
        ((p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 +
          (p.2.2 - q.2.2) ^ 2)) * (2 * (p.2.2 - q.2.2))) p.2.2 := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sqrt hsne).comp p.2.2 hSz
  have hx := (((hasDerivAt_id p.1).sub_const q.1).div hrootX hdne).deriv
  have hy := (((hasDerivAt_id p.2.1).sub_const q.2.1).div hrootY hdne).deriv
  have hz := (((hasDerivAt_id p.2.2).sub_const q.2.2).div hrootZ hdne).deriv
  simp only [id_eq] at hx hy hz
  change
    deriv (fun x : ℝ =>
      (x - q.1) / Real.sqrt
        ((x - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 +
          (p.2.2 - q.2.2) ^ 2)) p.1 = _ at hx
  change
    deriv (fun y : ℝ =>
      (y - q.2.1) / Real.sqrt
        ((p.1 - q.1) ^ 2 + (y - q.2.1) ^ 2 +
          (p.2.2 - q.2.2) ^ 2)) p.2.1 = _ at hy
  change
    deriv (fun z : ℝ =>
      (z - q.2.2) / Real.sqrt
        ((p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 +
          (z - q.2.2) ^ 2)) p.2.2 = _ at hz
  unfold radialDivergence divergence partialX partialY partialZ radialUnit distance
  change
    deriv (fun x : ℝ =>
      (x - q.1) / Real.sqrt
        ((x - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 +
          (p.2.2 - q.2.2) ^ 2)) p.1 +
      deriv (fun y : ℝ =>
        (y - q.2.1) / Real.sqrt
          ((p.1 - q.1) ^ 2 + (y - q.2.1) ^ 2 +
            (p.2.2 - q.2.2) ^ 2)) p.2.1 +
      deriv (fun z : ℝ =>
        (z - q.2.2) / Real.sqrt
          ((p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 +
            (z - q.2.2) ^ 2)) p.2.2 =
      2 / Real.sqrt
        ((p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 +
          (p.2.2 - q.2.2) ^ 2)
  rw [hx, hy, hz]
  field_simp [Real.sqrt_ne_zero'.2 hspos]
  nlinarith [Real.sq_sqrt (le_of_lt hspos)]

theorem gap1 (q p n : Vec3) (hpq : p ≠ q) :
    normalComponent q p n =
      (radialUnit q p).1 * n.1 +
        (radialUnit q p).2.1 * n.2.1 +
        (radialUnit q p).2.2 * n.2.2 := by
  rfl

theorem gap2 (q p : Vec3) (hpq : p ≠ q) :
    (radialUnit q p).1 = (p.1 - q.1) / distance q p := by
  rfl

theorem gap3 (q p : Vec3) (hpq : p ≠ q) :
    (radialUnit q p).2.1 = (p.2.1 - q.2.1) / distance q p := by
  rfl

theorem gap4 (q p : Vec3) (hpq : p ≠ q) :
    (radialUnit q p).2.2 = (p.2.2 - q.2.2) / distance q p := by
  rfl

theorem gap5 (q p n : Vec3) (hpq : p ≠ q) :
    normalComponent q p n =
      (p.1 - q.1) / distance q p * n.1 +
        (p.2.1 - q.2.1) / distance q p * n.2.1 +
        (p.2.2 - q.2.2) / distance q p * n.2.2 := by
  rfl

theorem gap6 (V : Set Vec3) (q : Vec3) (I : SurfaceIntegral)
    (normal : Vec3 → Vec3) (hq : q ∉ V)
    (hGauss : SatisfiesGaussOn V I normal) :
    boundaryRadialFlux I q normal = divergenceVolume V q := by
  change surfaceFlux I (radialUnit q) normal = divergenceVolume V q
  apply hGauss
  intro p hp
  have hpq : p ≠ q := by
    intro h
    apply hq
    simpa [h] using hp
  exact (radialRegular q p hpq).2.1

theorem gap7 (V : Set Vec3) (q : Vec3) (hq : q ∉ V) :
    divergenceVolume V q = 2 * inverseDistanceVolume V q := by
  unfold divergenceVolume inverseDistanceVolume
  calc
    (∫ p in V, radialDivergence q p) =
        ∫ p in V, 2 * (1 / distance q p) := by
          apply MeasureTheory.integral_congr_ae
          have hne : ∀ᵐ p : Vec3 ∂(volume.restrict V), p ≠ q := by
            apply ae_iff.2
            have hs : {p : Vec3 | ¬ p ≠ q} = {q} := by
              ext p
              simp
            rw [hs]
            rw [Measure.restrict_apply (measurableSet_singleton q)]
            simp [hq]
          filter_upwards [hne] with p hp
          rw [(radialRegular q p hp).2.2]
          ring
    _ = 2 * ∫ p in V, 1 / distance q p := by
          rw [MeasureTheory.integral_const_mul]

theorem gap8 (V : Set Vec3) (q : Vec3) (I : SurfaceIntegral)
    (normal : Vec3 → Vec3) (hq : q ∉ V)
    (hGauss : SatisfiesGaussOn V I normal) :
    inverseDistanceVolume V q =
      1 / 2 * boundaryRadialFlux I q normal := by
  have h₁ := gap6 V q I normal hq hGauss
  have h₂ := gap7 V q hq
  nlinarith

theorem gap9 (V : Set Vec3) (q : Vec3) (I : SurfaceIntegral)
    (normal : Vec3 → Vec3) (ε : ℝ) (hq : q ∈ V) (hε : 0 < ε)
    (hBall : closedBall3 q ε ⊆ interior V)
    (hPuncturedGauss : SatisfiesPuncturedGauss V I normal) :
    boundaryRadialFlux I q normal + innerSphereFlux q ε =
      2 * puncturedPotential V q ε := by
  have hdiff : ∀ p ∈ V \ deletedBall q ε,
      DifferentiableAt ℝ (radialUnit q) p := by
    intro p hp
    have hpq : p ≠ q := by
      intro h
      subst p
      apply hp.2
      simp [deletedBall, distance, hε]
    exact (radialRegular q p hpq).2.1
  have hG := hPuncturedGauss (radialUnit q) q ε hε hBall hdiff
  have hD := gap7 (V \ deletedBall q ε) q (by
    intro hqmem
    exact hqmem.2 (by simp [deletedBall, distance, hε]))
  simpa [boundaryRadialFlux, surfaceFlux, normalComponent,
    innerSphereFlux, puncturedPotential, divergenceVolume,
    inverseDistanceVolume] using hG.trans hD

theorem gap10 (q : Vec3) (ε : ℝ) (hε : 0 < ε) :
    innerSphereFlux q ε = -4 * Real.pi * ε ^ 2 := by
  have hdist : ∀ θ φ : ℝ, distance q (spherePoint q ε θ φ) = ε := by
    intro θ φ
    have htrig :
        Real.sin φ ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) +
            Real.cos φ ^ 2 = 1 := by
      rw [Real.cos_sq_add_sin_sq]
      nlinarith [Real.sin_sq_add_cos_sq φ]
    unfold distance spherePoint
    simp only [add_sub_cancel_left]
    rw [show
      (ε * Real.sin φ * Real.cos θ) ^ 2 +
          (ε * Real.sin φ * Real.sin θ) ^ 2 +
          (ε * Real.cos φ) ^ 2 = ε ^ 2 by
        calc
          (ε * Real.sin φ * Real.cos θ) ^ 2 +
                (ε * Real.sin φ * Real.sin θ) ^ 2 +
                (ε * Real.cos φ) ^ 2 =
              ε ^ 2 *
                (Real.sin φ ^ 2 *
                    (Real.cos θ ^ 2 + Real.sin θ ^ 2) +
                  Real.cos φ ^ 2) := by ring
          _ = ε ^ 2 := by rw [htrig]; ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hε]
  have hdot : ∀ θ φ : ℝ,
      dot (radialUnit q (spherePoint q ε θ φ))
          (inwardSphereAreaVector ε θ φ) =
        -ε ^ 2 * Real.sin φ := by
    intro θ φ
    have htrig :
        Real.sin φ ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) +
            Real.cos φ ^ 2 = 1 := by
      rw [Real.cos_sq_add_sin_sq]
      nlinarith [Real.sin_sq_add_cos_sq φ]
    have hdist' :
        distance q
          (q.1 + ε * Real.sin φ * Real.cos θ,
            q.2.1 + ε * Real.sin φ * Real.sin θ,
            q.2.2 + ε * Real.cos φ) = ε := by
      simpa only [spherePoint] using hdist θ φ
    unfold dot radialUnit inwardSphereAreaVector
    simp only [spherePoint, add_sub_cancel_left]
    rw [hdist']
    field_simp [ne_of_gt hε]
    linear_combination (-Real.sin φ) * htrig
  have hsin :
      (∫ φ in (0 : ℝ)..Real.pi, Real.sin φ) = 2 := by
    calc
      (∫ φ in (0 : ℝ)..Real.pi, Real.sin φ) =
          -Real.cos Real.pi - (-Real.cos 0) := by
            simpa only [neg_neg] using
              (intervalIntegral.integral_eq_sub_of_hasDerivAt
                (fun x _ => (Real.hasDerivAt_cos x).neg)
                (by
                  simpa only [neg_neg] using
                    (Real.continuous_sin.intervalIntegrable
                      (0 : ℝ) Real.pi)))
      _ = 2 := by rw [Real.cos_pi, Real.cos_zero]; ring
  unfold innerSphereFlux sphereFlux
  simp_rw [hdot]
  rw [intervalIntegral.integral_const_mul]
  rw [hsin]
  simp
  ring

theorem gap11 (V : Set Vec3) (q : Vec3)
    (hIntegrable : IntegrableOn (fun p => 1 / distance q p) V) :
    Tendsto (puncturedPotential V q) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (inverseDistanceVolume V q)) := by
  let f : Vec3 → ℝ := fun p => 1 / distance q p
  have hcont : Continuous (distance q) := by
    unfold distance
    fun_prop
  have hdel : ∀ ε : ℝ, MeasurableSet (deletedBall q ε) := by
    intro ε
    change MeasurableSet ((distance q) ⁻¹' Set.Iio ε)
    exact measurableSet_Iio.preimage hcont.measurable
  have ht : Tendsto
      (fun ε : ℝ => ∫ p in V, (deletedBall q ε)ᶜ.indicator f p)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ p in V, f p)) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (bound := fun p => ‖f p‖)
    · exact Filter.Eventually.of_forall (fun ε =>
        hIntegrable.aestronglyMeasurable.indicator (hdel ε).compl)
    · exact Filter.Eventually.of_forall (fun ε =>
        Filter.Eventually.of_forall (fun p => by
          by_cases hp : p ∈ (deletedBall q ε)ᶜ
          · simp [Set.indicator, hp]
          · simp [Set.indicator, hp]))
    · exact hIntegrable.norm
    · exact Filter.Eventually.of_forall (fun p => by
        by_cases hpq : p = q
        · subst p
          have hc : Tendsto (fun _ : ℝ => f q)
              (nhdsWithin 0 (Set.Ioi 0)) (nhds (f q)) :=
            tendsto_const_nhds
          refine hc.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with ε hε
          simp only [Set.mem_Ioi] at hε
          simp [f, deletedBall, distance, Set.indicator, hε]
        · have hdpos : 0 < distance q p := (radialRegular q p hpq).1
          have hc : Tendsto (fun _ : ℝ => f p)
              (nhdsWithin 0 (Set.Ioi 0)) (nhds (f p)) :=
            tendsto_const_nhds
          refine hc.congr' ?_
          filter_upwards [Filter.Eventually.filter_mono inf_le_left
              (eventually_lt_nhds hdpos)] with ε hε
          have hpcomp : p ∈ (deletedBall q ε)ᶜ := by
            change ¬ distance q p < ε
            exact not_lt_of_ge (le_of_lt hε)
          rw [Set.indicator_of_mem hpcomp])
  have hpunct : ∀ ε : ℝ, puncturedPotential V q ε =
      ∫ p in V, (deletedBall q ε)ᶜ.indicator f p := by
    intro ε
    unfold puncturedPotential
    rw [MeasureTheory.integral_indicator (μ := volume.restrict V)
      (hdel ε).compl]
    simp [Set.diff_eq, Measure.restrict_restrict, hdel ε,
      f, Set.inter_comm]
  have ht' := ht.congr'
    (Filter.Eventually.of_forall (fun ε => (hpunct ε).symm))
  simpa [f, inverseDistanceVolume] using ht'

theorem gap12 (V : Set Vec3) (q : Vec3) (I : SurfaceIntegral)
    (normal : Vec3 → Vec3) (hq : q ∈ V)
    (hInterior :
      ∃ ε₀ > 0, closedBall3 q ε₀ ⊆ interior V)
    (hPunctured : SatisfiesPuncturedGauss V I normal)
    (hIntegrable : IntegrableOn (fun p => 1 / distance q p) V) :
    inverseDistanceVolume V q =
      1 / 2 * boundaryRadialFlux I q normal := by
  rcases hInterior with ⟨ε₀, hε₀, hBall₀⟩
  let F := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hpos : ∀ᶠ ε : ℝ in F, 0 < ε := self_mem_nhdsWithin
  have hlt : ∀ᶠ ε : ℝ in F, ε < ε₀ :=
    Filter.Eventually.filter_mono inf_le_left (eventually_lt_nhds hε₀)
  have hballs : ∀ᶠ ε : ℝ in F,
      closedBall3 q ε ⊆ interior V := by
    filter_upwards [hpos, hlt] with ε hε hεlt
    intro p hp
    apply hBall₀
    exact le_trans hp (le_of_lt hεlt)
  have heq : ∀ᶠ ε : ℝ in F,
      boundaryRadialFlux I q normal + innerSphereFlux q ε =
        2 * puncturedPotential V q ε := by
    filter_upwards [hpos, hballs] with ε hε hb
    exact gap9 V q I normal ε hq hε hb hPunctured
  have hid : Tendsto (fun ε : ℝ => ε) F (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hinPoly : Tendsto (fun ε : ℝ => -4 * Real.pi * ε ^ 2)
      F (nhds 0) := by
    simpa using (hid.pow 2).const_mul (-4 * Real.pi)
  have hinFormula :
      (fun ε : ℝ => -4 * Real.pi * ε ^ 2) =ᶠ[F]
        innerSphereFlux q := by
    filter_upwards [hpos] with ε hε
    exact (gap10 q ε hε).symm
  have hin : Tendsto (innerSphereFlux q) F (nhds 0) :=
    hinPoly.congr' hinFormula
  have hleft : Tendsto
      (fun ε => boundaryRadialFlux I q normal + innerSphereFlux q ε)
      F (nhds (boundaryRadialFlux I q normal)) := by
    simpa using tendsto_const_nhds.add hin
  have hright : Tendsto (fun ε => 2 * puncturedPotential V q ε)
      F (nhds (2 * inverseDistanceVolume V q)) := by
    simpa using (gap11 V q hIntegrable).const_mul 2
  have hright' : Tendsto (fun ε => 2 * puncturedPotential V q ε)
      F (nhds (boundaryRadialFlux I q normal)) :=
    hleft.congr' heq
  have hlim := tendsto_nhds_unique hright' hright
  nlinarith

theorem gap13 (V : Set Vec3) (q : Vec3) (I : SurfaceIntegral)
    (normal : Vec3 → Vec3)
    (hOutside :
      q ∉ V →
        inverseDistanceVolume V q =
          1 / 2 * boundaryRadialFlux I q normal)
    (hInside :
      q ∈ V →
        inverseDistanceVolume V q =
          1 / 2 * boundaryRadialFlux I q normal) :
    inverseDistanceVolume V q =
      1 / 2 * boundaryRadialFlux I q normal := by
  by_cases hq : q ∈ V
  · exact hInside hq
  · exact hOutside hq

end

end ProofGap.Exercise4391
