import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4141

noncomputable section

open MeasureTheory Set
open scoped Interval Matrix

abbrev Point3 := Fin 3 → ℝ

def superellipsoid (a b c n : ℝ) : Set Point3 :=
  {p |
    0 ≤ p 0 ∧ 0 ≤ p 1 ∧ 0 ≤ p 2 ∧
      Real.rpow (p 0 / a) n +
        Real.rpow (p 1 / b) n +
          Real.rpow (p 2 / c) n ≤ 1}

def parameterization (a b c n : ℝ) (q : Point3) : Point3 :=
  let r := q 0
  let φ := q 1
  let ψ := q 2
  ![
    a * r *
      Real.rpow (Real.cos φ) (2 / n) *
        Real.rpow (Real.cos ψ) (2 / n),
    b * r *
      Real.rpow (Real.sin φ) (2 / n) *
        Real.rpow (Real.cos ψ) (2 / n),
    c * r * Real.rpow (Real.sin ψ) (2 / n)]

def coordinateJacobian
    (F : Point3 → Point3) (p : Point3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => deriv (fun t => F (Function.update p j t) i) (p j)

def jacobianAbs (F : Point3 → Point3) (p : Point3) : ℝ :=
  |Matrix.det (coordinateJacobian F p)|

def jacobianDensity (a b c n r φ ψ : ℝ) : ℝ :=
  4 / n ^ 2 * a * b * c * r ^ 2 *
    Real.rpow (Real.sin φ) (2 / n - 1) *
    Real.rpow (Real.cos φ) (2 / n - 1) *
    Real.rpow (Real.cos ψ) (4 / n - 1) *
    Real.rpow (Real.sin ψ) (2 / n - 1)

def mass (a b c n : ℝ) : ℝ :=
  ∫ _p in superellipsoid a b c n, (1 : ℝ)

def xCentroid (a b c n : ℝ) : ℝ :=
  1 / mass a b c n * ∫ p in superellipsoid a b c n, p 0

def yCentroid (a b c n : ℝ) : ℝ :=
  1 / mass a b c n * ∫ p in superellipsoid a b c n, p 1

def zCentroid (a b c n : ℝ) : ℝ :=
  1 / mass a b c n * ∫ p in superellipsoid a b c n, p 2

namespace TupleModel

private abbrev Point3 := ℝ × ℝ × ℝ

private def solid (a b c n : ℝ) : Set Point3 :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧
    Real.rpow (p.1 / a) n +
      Real.rpow (p.2.1 / b) n +
      Real.rpow (p.2.2 / c) n ≤ 1}

private def mass (a b c n : ℝ) : ℝ :=
  ∫ _p in solid a b c n, (1 : ℝ) ∂MeasureTheory.volume

private def centroid (a b c n : ℝ) : Point3 :=
  ((∫ p in solid a b c n, p.1 ∂MeasureTheory.volume) / mass a b c n,
    (∫ p in solid a b c n, p.2.1 ∂MeasureTheory.volume) / mass a b c n,
    (∫ p in solid a b c n, p.2.2 ∂MeasureTheory.volume) / mass a b c n)

private def centroidFactor (n : ℝ) : ℝ :=
  3 / 4 *
    (Real.Gamma (2 / n) * Real.Gamma (3 / n)) /
      (Real.Gamma (1 / n) * Real.Gamma (4 / n))

private def betaFn (x y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    Real.rpow (1 - t) (x - 1) * Real.rpow t (y - 1)

private theorem betaFn_eq_Gamma_mul_div
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    betaFn x y =
      Real.Gamma x * Real.Gamma y / Real.Gamma (x + y) := by
  unfold betaFn
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  calc
    (∫ t in (0 : ℝ)..1,
        ((Real.rpow (1 - t) (x - 1) *
          Real.rpow t (y - 1) : ℝ) : ℂ)) =
        Complex.betaIntegral (y : ℂ) (x : ℂ) := by
      rw [Complex.betaIntegral]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      change
        ((Real.rpow (1 - t) (x - 1) *
          Real.rpow t (y - 1) : ℝ) : ℂ) =
          (t : ℂ) ^ ((y : ℂ) - 1) *
            (1 - (t : ℂ)) ^ ((x : ℂ) - 1)
      have hpow1 :=
        Complex.ofReal_cpow (sub_nonneg.mpr ht.2) (x - 1)
      have hpow2 :=
        Complex.ofReal_cpow ht.1 (y - 1)
      rw [Real.rpow_eq_pow, Real.rpow_eq_pow,
        Complex.ofReal_mul, hpow1, hpow2]
      push_cast
      ring
    _ = Complex.Gamma (y : ℂ) * Complex.Gamma (x : ℂ) /
          Complex.Gamma ((y : ℂ) + (x : ℂ)) :=
      Complex.betaIntegral_eq_Gamma_mul_div
        (y : ℂ) (x : ℂ) (by simpa) (by simpa)
    _ = ((Real.Gamma x * Real.Gamma y /
          Real.Gamma (x + y) : ℝ) : ℂ) := by
      rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal,
        ← Complex.ofReal_add, Complex.Gamma_ofReal]
      push_cast
      ring

private theorem rpow_substitution_factor
    (n k r : ℝ) (hn : 0 < n) (hr : 0 < r) :
    Real.rpow (Real.rpow r n) (k / n - 1) *
        (n * Real.rpow r (n - 1)) =
      n * Real.rpow r (k - 1) := by
  have hpow :
      Real.rpow (Real.rpow r n) (k / n - 1) =
        Real.rpow r (n * (k / n - 1)) := by
    exact (Real.rpow_mul hr.le n (k / n - 1)).symm
  have hexp :
      n * (k / n - 1) + (n - 1) = k - 1 := by
    field_simp [hn.ne']
    ring
  rw [hpow]
  calc
    Real.rpow r (n * (k / n - 1)) *
        (n * Real.rpow r (n - 1)) =
      n * (Real.rpow r (n * (k / n - 1)) *
        Real.rpow r (n - 1)) := by ring
    _ = n * Real.rpow r
        (n * (k / n - 1) + (n - 1)) := by
      exact congrArg (fun z : ℝ => n * z)
        (Real.rpow_add hr
          (n * (k / n - 1)) (n - 1)).symm
    _ = n * Real.rpow r (k - 1) := by rw [hexp]

private theorem unit_rpow_weight_integral
    (n alpha k : ℝ) (hn : 0 < n) :
    (∫ r in (0 : ℝ)..1,
        Real.rpow r (k - 1) *
          Real.rpow (1 - Real.rpow r n) alpha) =
      1 / n * betaFn (alpha + 1) (k / n) := by
  let kernel : ℝ → ℝ :=
    fun t =>
      Real.rpow (1 - t) alpha *
        Real.rpow t (k / n - 1)
  let g : ℝ → ℝ :=
    fun t => (Set.Iic (1 : ℝ)).indicator kernel t
  let radial : ℝ → ℝ :=
    fun r =>
      Real.rpow r (k - 1) *
        Real.rpow (1 - Real.rpow r n) alpha
  let rDomain : Set ℝ :=
    {r | Real.rpow r n ≤ 1}
  have hrDomain : MeasurableSet rDomain := by
    dsimp [rDomain]
    exact
      measurableSet_le
        (Real.continuous_rpow_const hn.le).measurable
        measurable_const
  have hsub :
      (∫ r in Set.Ioi (0 : ℝ),
          (n * Real.rpow r (n - 1)) *
            g (Real.rpow r n)) =
        ∫ t in Set.Ioi (0 : ℝ), g t := by
    simpa only [smul_eq_mul] using
      (integral_comp_rpow_Ioi_of_pos
        (g := g) hn)
  have hright :
      (∫ t in Set.Ioi (0 : ℝ), g t) =
        betaFn (alpha + 1) (k / n) := by
    dsimp [g]
    rw [setIntegral_indicator measurableSet_Iic]
    have hinter :
        Set.Ioi (0 : ℝ) ∩ Set.Iic 1 =
          Set.Ioc 0 1 := by
      ext t
      simp [and_comm]
    rw [hinter]
    rw [← intervalIntegral.integral_of_le zero_le_one]
    unfold betaFn
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [kernel]
    congr 2 <;> ring
  have hdomain :
      Set.Ioi (0 : ℝ) ∩ rDomain =
        Set.Ioc 0 1 := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Ioi,
      Set.mem_Ioc, rDomain, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hr, hrpow⟩
      have hiff :=
        Real.rpow_le_rpow_iff hr.le zero_le_one hn
      have hrle : r ≤ 1 := by
        apply hiff.mp
        simpa only [Real.one_rpow] using hrpow
      exact ⟨hr, hrle⟩
    · rintro ⟨hr, hrle⟩
      refine ⟨hr, ?_⟩
      have hiff :=
        Real.rpow_le_rpow_iff hr.le zero_le_one hn
      have hp := hiff.mpr hrle
      simpa only [Real.one_rpow] using hp
  have hleft :
      (∫ r in Set.Ioi (0 : ℝ),
          (n * Real.rpow r (n - 1)) *
            g (Real.rpow r n)) =
        n * ∫ r in (0 : ℝ)..1, radial r := by
    calc
      (∫ r in Set.Ioi (0 : ℝ),
          (n * Real.rpow r (n - 1)) *
            g (Real.rpow r n)) =
          ∫ r in Set.Ioi (0 : ℝ),
            rDomain.indicator
              (fun r => n * radial r) r := by
        apply MeasureTheory.setIntegral_congr_fun
          measurableSet_Ioi
        intro r hr
        have hrpos : 0 < r := hr
        by_cases hd : r ∈ rDomain
        · have hp : Real.rpow r n ∈ Set.Iic (1 : ℝ) := hd
          rw [Set.indicator_of_mem hd]
          change
            (n * Real.rpow r (n - 1)) *
                g (Real.rpow r n) =
              n * radial r
          have hg :
              g (Real.rpow r n) =
                (Set.Iic (1 : ℝ)).indicator kernel
                  (Real.rpow r n) := rfl
          rw [hg, Set.indicator_of_mem hp]
          dsimp [kernel, radial]
          have hfactor :=
            rpow_substitution_factor n k r hn hrpos
          calc
            (n * Real.rpow r (n - 1)) *
                (Real.rpow
                    (1 - Real.rpow r n) alpha *
                  Real.rpow (Real.rpow r n)
                    (k / n - 1)) =
              Real.rpow
                  (1 - Real.rpow r n) alpha *
                (Real.rpow (Real.rpow r n)
                    (k / n - 1) *
                  (n * Real.rpow r (n - 1))) := by
                ring
            _ = Real.rpow
                  (1 - Real.rpow r n) alpha *
                (n * Real.rpow r (k - 1)) := by
                rw [hfactor]
            _ = n *
                (Real.rpow r (k - 1) *
                  Real.rpow
                    (1 - Real.rpow r n) alpha) := by
                ring
        · have hp : Real.rpow r n ∉ Set.Iic (1 : ℝ) := hd
          rw [Set.indicator_of_notMem hd]
          change
            (n * Real.rpow r (n - 1)) *
                g (Real.rpow r n) =
              0
          have hg :
              g (Real.rpow r n) =
                (Set.Iic (1 : ℝ)).indicator kernel
                  (Real.rpow r n) := rfl
          rw [hg, Set.indicator_of_notMem hp]
          simp
      _ = ∫ r in Set.Ioi (0 : ℝ) ∩ rDomain,
          n * radial r := by
        rw [setIntegral_indicator hrDomain]
      _ = ∫ r in Set.Ioc (0 : ℝ) 1,
          n * radial r := by
        rw [hdomain]
      _ = ∫ r in (0 : ℝ)..1,
          n * radial r := by
        rw [intervalIntegral.integral_of_le zero_le_one]
      _ = n * ∫ r in (0 : ℝ)..1, radial r := by
        rw [intervalIntegral.integral_const_mul]
  rw [hleft, hright] at hsub
  dsimp [radial] at hsub ⊢
  rw [← hsub]
  field_simp [hn.ne']

private theorem unit_rpow_integral
    (n alpha : ℝ) (hn : 0 < n) :
    (∫ r in (0 : ℝ)..1,
        Real.rpow (1 - Real.rpow r n) alpha) =
      1 / n * betaFn (alpha + 1) (1 / n) := by
  simpa using unit_rpow_weight_integral n alpha 1 hn

private theorem unit_rpow_first_moment_integral
    (n alpha : ℝ) (hn : 0 < n) :
    (∫ r in (0 : ℝ)..1,
        r * Real.rpow (1 - Real.rpow r n) alpha) =
      1 / n * betaFn (alpha + 1) (2 / n) := by
  convert unit_rpow_weight_integral n alpha 2 hn using 1 <;>
    norm_num [Real.rpow_one]

private def baseRegion (a b n : ℝ) : Set (ℝ × ℝ) :=
  {p |
    0 ≤ p.1 ∧ 0 ≤ p.2 ∧
      Real.rpow (p.1 / a) n +
        Real.rpow (p.2 / b) n ≤ 1}

private def residual (a n x : ℝ) : ℝ :=
  1 - Real.rpow (x / a) n

private def ordinateBound (a b n x : ℝ) : ℝ :=
  b * Real.rpow (residual a n x) (1 / n)

private def baseResidual
    (a b n x y : ℝ) : ℝ :=
  1 -
    (Real.rpow (x / a) n +
      Real.rpow (y / b) n)

private def capHeight
    (a b c n x y : ℝ) : ℝ :=
  c * Real.rpow (baseResidual a b n x y) (1 / n)

private theorem rpow_one_div_rpow
    (z n : ℝ) (hn : 0 < n) (hz : 0 ≤ z) :
    Real.rpow (Real.rpow z (1 / n)) n = z := by
  calc
    Real.rpow (Real.rpow z (1 / n)) n =
        Real.rpow z ((1 / n) * n) := by
      exact (Real.rpow_mul hz (1 / n) n).symm
    _ = Real.rpow z 1 := by
      congr 1
      field_simp [hn.ne']
    _ = z := Real.rpow_one z

private theorem baseRegion_closed
    (a b n : ℝ) (hn : 0 < n) :
    IsClosed (baseRegion a b n) := by
  have hx :
      Continuous (fun p : ℝ × ℝ =>
        Real.rpow (p.1 / a) n) :=
    (Real.continuous_rpow_const hn.le).comp
      (continuous_fst.div_const a)
  have hy :
      Continuous (fun p : ℝ × ℝ =>
        Real.rpow (p.2 / b) n) :=
    (Real.continuous_rpow_const hn.le).comp
      (continuous_snd.div_const b)
  unfold baseRegion
  exact
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le (hx.add hy) continuous_const))

private theorem baseRegion_compact
    (a b n : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hn : 0 < n) :
    IsCompact (baseRegion a b n) := by
  apply
    (isCompact_Icc :
      IsCompact
        (Set.Icc ((0 : ℝ), (0 : ℝ)) (a, b))).of_isClosed_subset
      (baseRegion_closed a b n hn)
  rintro ⟨x, y⟩ hp
  change
    0 ≤ x ∧ 0 ≤ y ∧
      Real.rpow (x / a) n +
        Real.rpow (y / b) n ≤ 1 at hp
  have hxratio : 0 ≤ x / a := div_nonneg hp.1 ha.le
  have hyratio : 0 ≤ y / b := div_nonneg hp.2.1 hb.le
  have hxpow0 : 0 ≤ Real.rpow (x / a) n :=
    Real.rpow_nonneg hxratio _
  have hypow0 : 0 ≤ Real.rpow (y / b) n :=
    Real.rpow_nonneg hyratio _
  have hxpow1 : Real.rpow (x / a) n ≤ 1 := by
    linarith
  have hypow1 : Real.rpow (y / b) n ≤ 1 := by
    linarith
  have hxratio1 : x / a ≤ 1 := by
    have hiff :=
      Real.rpow_le_rpow_iff hxratio zero_le_one hn
    exact hiff.mp (by simpa only [Real.one_rpow] using hxpow1)
  have hyratio1 : y / b ≤ 1 := by
    have hiff :=
      Real.rpow_le_rpow_iff hyratio zero_le_one hn
    exact hiff.mp (by simpa only [Real.one_rpow] using hypow1)
  have hxa : x ≤ a := (div_le_one ha).mp hxratio1
  have hyb : y ≤ b := (div_le_one hb).mp hyratio1
  exact ⟨⟨hp.1, hp.2.1⟩, ⟨hxa, hyb⟩⟩

private theorem residual_nonneg
    (a n x : ℝ) (ha : 0 < a) (hn : 0 < n)
    (hx : x ∈ Set.Icc (0 : ℝ) a) :
    0 ≤ residual a n x := by
  have hxratio0 : 0 ≤ x / a := div_nonneg hx.1 ha.le
  have hxratio1 : x / a ≤ 1 :=
    (div_le_one ha).mpr hx.2
  have hp :=
    (Real.rpow_le_rpow_iff hxratio0 zero_le_one hn).mpr
      hxratio1
  dsimp [residual]
  simpa only [Real.one_rpow] using sub_nonneg.mpr hp

private theorem ordinateBound_nonneg
    (a b n x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hn : 0 < n) (hx : x ∈ Set.Icc (0 : ℝ) a) :
    0 ≤ ordinateBound a b n x := by
  unfold ordinateBound
  exact
    mul_nonneg hb.le
      (Real.rpow_nonneg
        (residual_nonneg a n x ha hn hx) _)

private theorem base_first_mem
    (a b n x y : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hn : 0 < n)
    (hp : (x, y) ∈ baseRegion a b n) :
    x ∈ Set.Icc (0 : ℝ) a := by
  change
    0 ≤ x ∧ 0 ≤ y ∧
      Real.rpow (x / a) n +
        Real.rpow (y / b) n ≤ 1 at hp
  have hxratio0 : 0 ≤ x / a := div_nonneg hp.1 ha.le
  have hypow0 : 0 ≤ Real.rpow (y / b) n :=
    Real.rpow_nonneg (div_nonneg hp.2.1 hb.le) _
  have hxpow1 : Real.rpow (x / a) n ≤ 1 := by
    linarith
  have hxratio1 : x / a ≤ 1 := by
    exact
      (Real.rpow_le_rpow_iff hxratio0 zero_le_one hn).mp
        (by simpa only [Real.one_rpow] using hxpow1)
  exact ⟨hp.1, (div_le_one ha).mp hxratio1⟩

private theorem base_section_iff
    (a b n x y : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hn : 0 < n) (hx : x ∈ Set.Icc (0 : ℝ) a) :
    (x, y) ∈ baseRegion a b n ↔
      y ∈ Set.Icc (0 : ℝ) (ordinateBound a b n x) := by
  let L : ℝ := residual a n x
  let q : ℝ := Real.rpow L (1 / n)
  have hL : 0 ≤ L := residual_nonneg a n x ha hn hx
  have hq : 0 ≤ q := Real.rpow_nonneg hL _
  have hqn : Real.rpow q n = L := by
    dsimp [q]
    exact rpow_one_div_rpow L n hn hL
  have hqnPow : q ^ n = L := by
    simpa only [← Real.rpow_eq_pow] using hqn
  constructor
  · intro hp
    change
      0 ≤ x ∧ 0 ≤ y ∧
        Real.rpow (x / a) n +
          Real.rpow (y / b) n ≤ 1 at hp
    simp only [Real.rpow_eq_pow] at hp
    have hyratio0 : 0 ≤ y / b := div_nonneg hp.2.1 hb.le
    have hypowle :
        (y / b) ^ n ≤ L := by
      dsimp [L, residual]
      linarith
    have hyratioq : y / b ≤ q := by
      apply
        (Real.rpow_le_rpow_iff hyratio0 hq hn).mp
      rw [hqnPow]
      exact hypowle
    refine ⟨hp.2.1, ?_⟩
    have hy : y ≤ q * b := (div_le_iff₀ hb).mp hyratioq
    simpa [ordinateBound, q, L, mul_comm] using hy
  · intro hy
    have hyratio0 : 0 ≤ y / b := div_nonneg hy.1 hb.le
    have hyratioq : y / b ≤ q := by
      apply (div_le_iff₀ hb).mpr
      simpa [ordinateBound, q, L, mul_comm] using hy.2
    have hypowle : (y / b) ^ n ≤ L := by
      have hp :=
        (Real.rpow_le_rpow_iff hyratio0 hq hn).mpr
          hyratioq
      rwa [hqnPow] at hp
    change
      0 ≤ x ∧ 0 ≤ y ∧
        Real.rpow (x / a) n +
          Real.rpow (y / b) n ≤ 1
    refine ⟨hx.1, hy.1, ?_⟩
    dsimp [L, residual] at hypowle
    simp only [Real.rpow_eq_pow]
    linarith

private theorem base_indicator_integrable
    (a b n : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hn : 0 < n) (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) :
    Integrable ((baseRegion a b n).indicator f) := by
  rw [integrable_indicator_iff
    (baseRegion_closed a b n hn).measurableSet]
  exact hf.continuousOn.integrableOn_compact
    (baseRegion_compact a b n ha hb hn)

private theorem base_vertical_section_integral
    (a b n x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hn : 0 < n) (f : ℝ × ℝ → ℝ) :
    (∫ y : ℝ,
        (baseRegion a b n).indicator f (x, y)) =
      (Set.Icc (0 : ℝ) a).indicator
        (fun u =>
          ∫ y in (0 : ℝ)..ordinateBound a b n u,
            f (u, y)) x := by
  by_cases hx : x ∈ Set.Icc (0 : ℝ) a
  · have hmem (y : ℝ) :
        (x, y) ∈ baseRegion a b n ↔
          y ∈ Set.Icc (0 : ℝ) (ordinateBound a b n x) :=
      base_section_iff a b n x y ha hb hn hx
    have hfun :
        (fun y : ℝ =>
          (baseRegion a b n).indicator f (x, y)) =
          (Set.Icc (0 : ℝ) (ordinateBound a b n x)).indicator
            (fun y => f (x, y)) := by
      funext y
      by_cases hy :
          y ∈ Set.Icc (0 : ℝ) (ordinateBound a b n x)
      · have hp : (x, y) ∈ baseRegion a b n :=
          (hmem y).mpr hy
        rw [Set.indicator_of_mem hp,
          Set.indicator_of_mem hy]
      · have hp : (x, y) ∉ baseRegion a b n := by
          exact fun h => hy ((hmem y).mp h)
        rw [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem hy]
    rw [hfun,
      MeasureTheory.integral_indicator measurableSet_Icc,
      integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le
      (ordinateBound_nonneg a b n x ha hb hn hx)]
    rw [Set.indicator_of_mem hx]
  · have hnone (y : ℝ) :
        (x, y) ∉ baseRegion a b n := by
      intro hp
      exact hx (base_first_mem a b n x y ha hb hn hp)
    have hfun :
        (fun y : ℝ =>
          (baseRegion a b n).indicator f (x, y)) =
          fun _y : ℝ => 0 := by
      funext y
      rw [Set.indicator_of_notMem (hnone y)]
    rw [hfun, Set.indicator_of_notMem hx]
    simp

private theorem base_integral_as_iterated
    (a b n : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hn : 0 < n) (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) :
    (∫ p in baseRegion a b n, f p) =
      ∫ x in (0 : ℝ)..a,
        ∫ y in (0 : ℝ)..ordinateBound a b n x,
          f (x, y) := by
  have hmeas : MeasurableSet (baseRegion a b n) :=
    (baseRegion_closed a b n hn).measurableSet
  have hfi :
      Integrable ((baseRegion a b n).indicator f) :=
    base_indicator_integrable a b n ha hb hn f hf
  calc
    (∫ p in baseRegion a b n, f p) =
        ∫ p : ℝ × ℝ,
          (baseRegion a b n).indicator f p := by
      rw [MeasureTheory.integral_indicator hmeas]
    _ = ∫ x : ℝ, ∫ y : ℝ,
          (baseRegion a b n).indicator f (x, y) := by
      rw [Measure.volume_eq_prod] at hfi ⊢
      exact MeasureTheory.integral_prod
        ((baseRegion a b n).indicator f) hfi
    _ = ∫ x : ℝ,
          (Set.Icc (0 : ℝ) a).indicator
            (fun u =>
              ∫ y in (0 : ℝ)..ordinateBound a b n u,
                f (u, y)) x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        base_vertical_section_integral
          a b n x ha hb hn f
    _ = ∫ x in Set.Icc (0 : ℝ) a,
          ∫ y in (0 : ℝ)..ordinateBound a b n x,
            f (x, y) := by
      rw [MeasureTheory.integral_indicator measurableSet_Icc]
    _ = ∫ x in (0 : ℝ)..a,
          ∫ y in (0 : ℝ)..ordinateBound a b n x,
            f (x, y) := by
      rw [intervalIntegral.integral_of_le ha.le,
        integral_Icc_eq_integral_Ioc]

private theorem residual_scale
    (a n r : ℝ) (ha : 0 < a) :
    residual a n (a * r) =
      1 - Real.rpow r n := by
  have hdiv : a * r / a = r := by
    field_simp [ha.ne']
  unfold residual
  rw [hdiv]

private theorem baseResidual_scaled_ordinate
    (a b n x t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hn : 0 < n) (hx : x ∈ Set.Icc (0 : ℝ) a)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    baseResidual a b n x (ordinateBound a b n x * t) =
      residual a n x * (1 - Real.rpow t n) := by
  let L : ℝ := residual a n x
  let q : ℝ := Real.rpow L (1 / n)
  have hL : 0 ≤ L := residual_nonneg a n x ha hn hx
  have hq : 0 ≤ q := Real.rpow_nonneg hL _
  have hqn : Real.rpow q n = L :=
    rpow_one_div_rpow L n hn hL
  have hydiv :
      ordinateBound a b n x * t / b = q * t := by
    dsimp [ordinateBound, q, L]
    field_simp [hb.ne']
  have hypow :
      Real.rpow (ordinateBound a b n x * t / b) n =
        L * Real.rpow t n := by
    rw [hydiv]
    calc
      Real.rpow (q * t) n =
          Real.rpow q n * Real.rpow t n :=
        Real.mul_rpow hq ht.1
      _ = L * Real.rpow t n := by rw [hqn]
  have hxterm :
      Real.rpow (x / a) n = 1 - L := by
    dsimp [L, residual]
    ring
  unfold baseResidual
  rw [hxterm, hypow]
  ring

private theorem baseResidual_rpow_scaled
    (a b n alpha x t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (halpha : 0 ≤ alpha)
    (hx : x ∈ Set.Icc (0 : ℝ) a)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Real.rpow
        (baseResidual a b n x
          (ordinateBound a b n x * t)) alpha =
      Real.rpow (residual a n x) alpha *
        Real.rpow (1 - Real.rpow t n) alpha := by
  have hL : 0 ≤ residual a n x :=
    residual_nonneg a n x ha hn hx
  have htPowLe : Real.rpow t n ≤ 1 := by
    have hp :=
      (Real.rpow_le_rpow_iff ht.1 zero_le_one hn).mpr ht.2
    simpa only [Real.one_rpow] using hp
  have htResidual : 0 ≤ 1 - Real.rpow t n :=
    sub_nonneg.mpr htPowLe
  rw [baseResidual_scaled_ordinate
    a b n x t ha hb hn hx ht]
  exact Real.mul_rpow hL htResidual

private theorem inner_power_integral
    (a b n alpha x : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (halpha : 0 ≤ alpha)
    (hx : x ∈ Set.Icc (0 : ℝ) a) :
    (∫ y in (0 : ℝ)..ordinateBound a b n x,
        Real.rpow (baseResidual a b n x y) alpha) =
      b * Real.rpow (residual a n x) (alpha + 1 / n) *
        ∫ t in (0 : ℝ)..1,
          Real.rpow (1 - Real.rpow t n) alpha := by
  let B : ℝ := ordinateBound a b n x
  let L : ℝ := residual a n x
  let q : ℝ := Real.rpow L (1 / n)
  let J : ℝ :=
    ∫ t in (0 : ℝ)..1,
      Real.rpow (1 - Real.rpow t n) alpha
  have hscale :
      (∫ y in (0 : ℝ)..B,
          Real.rpow (baseResidual a b n x y) alpha) =
        B * ∫ t in (0 : ℝ)..1,
          Real.rpow (baseResidual a b n x (B * t)) alpha := by
    symm
    simpa only [mul_zero, mul_one] using
      (intervalIntegral.mul_integral_comp_mul_left
        (f := fun y =>
          Real.rpow (baseResidual a b n x y) alpha)
        (a := (0 : ℝ)) (b := 1) B)
  have hpoint :
      (∫ t in (0 : ℝ)..1,
          Real.rpow (baseResidual a b n x (B * t)) alpha) =
        Real.rpow L alpha * J := by
    calc
      _ = ∫ t in (0 : ℝ)..1,
          Real.rpow L alpha *
            Real.rpow (1 - Real.rpow t n) alpha := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
          simpa [Set.uIcc_of_le zero_le_one] using ht
        dsimp [B, L]
        exact baseResidual_rpow_scaled
          a b n alpha x t ha hb hn halpha hx ht'
      _ = Real.rpow L alpha * J := by
        rw [intervalIntegral.integral_const_mul]
  have hL : 0 ≤ L :=
    residual_nonneg a n x ha hn hx
  have hq :
      q = Real.rpow L (1 / n) := rfl
  have hpow :
      Real.rpow L alpha * q =
        Real.rpow L (alpha + 1 / n) := by
    rw [hq]
    exact (Real.rpow_add_of_nonneg hL
      halpha (one_div_pos.mpr hn).le).symm
  change
    (∫ y in (0 : ℝ)..B,
        Real.rpow (baseResidual a b n x y) alpha) =
      b * Real.rpow L (alpha + 1 / n) * J
  rw [hscale, hpoint]
  have hB : B = b * q := by rfl
  rw [hB, ← hpow]
  ring

private theorem inner_first_moment_integral
    (a b n alpha x : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (halpha : 0 ≤ alpha)
    (hx : x ∈ Set.Icc (0 : ℝ) a) :
    (∫ y in (0 : ℝ)..ordinateBound a b n x,
        y * Real.rpow (baseResidual a b n x y) alpha) =
      b ^ 2 *
        Real.rpow (residual a n x) (alpha + 2 / n) *
        ∫ t in (0 : ℝ)..1,
          t * Real.rpow (1 - Real.rpow t n) alpha := by
  let B : ℝ := ordinateBound a b n x
  let L : ℝ := residual a n x
  let q : ℝ := Real.rpow L (1 / n)
  let K : ℝ :=
    ∫ t in (0 : ℝ)..1,
      t * Real.rpow (1 - Real.rpow t n) alpha
  have hscale :
      (∫ y in (0 : ℝ)..B,
          y * Real.rpow (baseResidual a b n x y) alpha) =
        B * ∫ t in (0 : ℝ)..1,
          (B * t) *
            Real.rpow (baseResidual a b n x (B * t)) alpha := by
    symm
    simpa only [mul_zero, mul_one] using
      (intervalIntegral.mul_integral_comp_mul_left
        (f := fun y =>
          y * Real.rpow (baseResidual a b n x y) alpha)
        (a := (0 : ℝ)) (b := 1) B)
  have hpoint :
      (∫ t in (0 : ℝ)..1,
          (B * t) *
            Real.rpow (baseResidual a b n x (B * t)) alpha) =
        (B * Real.rpow L alpha) * K := by
    calc
      _ = ∫ t in (0 : ℝ)..1,
          (B * Real.rpow L alpha) *
            (t * Real.rpow (1 - Real.rpow t n) alpha) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
          simpa [Set.uIcc_of_le zero_le_one] using ht
        dsimp only
        have hs :
            Real.rpow (baseResidual a b n x (B * t)) alpha =
              Real.rpow L alpha *
                Real.rpow (1 - Real.rpow t n) alpha := by
          simpa only [B, L] using
            baseResidual_rpow_scaled
              a b n alpha x t ha hb hn halpha hx ht'
        rw [hs]
        ring
      _ = (B * Real.rpow L alpha) * K := by
        rw [intervalIntegral.integral_const_mul]
  have hL : 0 ≤ L :=
    residual_nonneg a n x ha hn hx
  have hexp : 0 ≤ 1 / n := (one_div_pos.mpr hn).le
  have hq2 :
      q * q = Real.rpow L (2 / n) := by
    dsimp [q]
    rw [← Real.rpow_add_of_nonneg hL hexp hexp]
    congr 1
    field_simp [hn.ne']
    ring
  have hpow :
      Real.rpow L alpha * (q * q) =
        Real.rpow L (alpha + 2 / n) := by
    rw [hq2]
    exact (Real.rpow_add_of_nonneg hL halpha
      (div_nonneg (by norm_num) hn.le)).symm
  change
    (∫ y in (0 : ℝ)..B,
        y * Real.rpow (baseResidual a b n x y) alpha) =
      b ^ 2 * Real.rpow L (alpha + 2 / n) * K
  rw [hscale, hpoint]
  have hB : B = b * q := by rfl
  rw [hB, ← hpow]
  ring

private theorem baseResidual_continuous
    (a b n : ℝ) (hn : 0 < n) :
    Continuous
      (fun p : ℝ × ℝ =>
        baseResidual a b n p.1 p.2) := by
  have hx :
      Continuous (fun p : ℝ × ℝ =>
        Real.rpow (p.1 / a) n) :=
    (Real.continuous_rpow_const hn.le).comp
      (continuous_fst.div_const a)
  have hy :
      Continuous (fun p : ℝ × ℝ =>
        Real.rpow (p.2 / b) n) :=
    (Real.continuous_rpow_const hn.le).comp
      (continuous_snd.div_const b)
  unfold baseResidual
  exact continuous_const.sub (hx.add hy)

private theorem base_power_factorization
    (a b n alpha : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (halpha : 0 ≤ alpha) :
    (∫ p in baseRegion a b n,
        Real.rpow
          (baseResidual a b n p.1 p.2) alpha) =
      a * b *
        (∫ r in (0 : ℝ)..1,
          Real.rpow
            (1 - Real.rpow r n) (alpha + 1 / n)) *
        (∫ t in (0 : ℝ)..1,
          Real.rpow (1 - Real.rpow t n) alpha) := by
  let J₀ : ℝ :=
    ∫ t in (0 : ℝ)..1,
      Real.rpow (1 - Real.rpow t n) alpha
  let J₁ : ℝ :=
    ∫ r in (0 : ℝ)..1,
      Real.rpow
        (1 - Real.rpow r n) (alpha + 1 / n)
  have hf : Continuous
      (fun p : ℝ × ℝ =>
        Real.rpow
          (baseResidual a b n p.1 p.2) alpha) :=
    (Real.continuous_rpow_const halpha).comp
      (baseResidual_continuous a b n hn)
  have hiter :=
    base_integral_as_iterated a b n ha hb hn _ hf
  have hinner :
      (∫ x in (0 : ℝ)..a,
          ∫ y in (0 : ℝ)..ordinateBound a b n x,
            Real.rpow (baseResidual a b n x y) alpha) =
        ∫ x in (0 : ℝ)..a,
          b *
            Real.rpow (residual a n x)
              (alpha + 1 / n) * J₀ := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) a := by
      simpa [Set.uIcc_of_le ha.le] using hx
    dsimp [J₀]
    exact inner_power_integral
      a b n alpha x ha hb hn halpha hx'
  have hpull :
      (∫ x in (0 : ℝ)..a,
          b *
            Real.rpow (residual a n x)
              (alpha + 1 / n) * J₀) =
        (b * J₀) *
          ∫ x in (0 : ℝ)..a,
            Real.rpow (residual a n x)
              (alpha + 1 / n) := by
    calc
      _ = ∫ x in (0 : ℝ)..a,
          (b * J₀) *
            Real.rpow (residual a n x)
              (alpha + 1 / n) := by
        apply intervalIntegral.integral_congr
        intro x hx
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul]
  have houter :
      (∫ x in (0 : ℝ)..a,
          Real.rpow (residual a n x)
            (alpha + 1 / n)) =
        a * J₁ := by
    have hscale :
        a *
            (∫ r in (0 : ℝ)..1,
              Real.rpow
                (residual a n (a * r))
                (alpha + 1 / n)) =
          ∫ x in (0 : ℝ)..a,
            Real.rpow (residual a n x)
              (alpha + 1 / n) := by
      simpa only [mul_zero, mul_one] using
        (intervalIntegral.mul_integral_comp_mul_left
          (f := fun x =>
            Real.rpow (residual a n x)
              (alpha + 1 / n))
          (a := (0 : ℝ)) (b := 1) a)
    rw [← hscale]
    apply congrArg (fun z : ℝ => a * z)
    dsimp [J₁]
    apply intervalIntegral.integral_congr
    intro r hr
    dsimp only
    change
      Real.rpow (residual a n (a * r))
          (alpha + 1 / n) =
        Real.rpow (1 - Real.rpow r n)
          (alpha + 1 / n)
    rw [residual_scale a n r ha]
  rw [hiter, hinner, hpull, houter]
  dsimp [J₀, J₁]
  ring

private theorem base_x_power_factorization
    (a b n alpha : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (halpha : 0 ≤ alpha) :
    (∫ p in baseRegion a b n,
        p.1 *
          Real.rpow
            (baseResidual a b n p.1 p.2) alpha) =
      a ^ 2 * b *
        (∫ r in (0 : ℝ)..1,
          r * Real.rpow
            (1 - Real.rpow r n) (alpha + 1 / n)) *
        (∫ t in (0 : ℝ)..1,
          Real.rpow (1 - Real.rpow t n) alpha) := by
  let J₀ : ℝ :=
    ∫ t in (0 : ℝ)..1,
      Real.rpow (1 - Real.rpow t n) alpha
  let K₁ : ℝ :=
    ∫ r in (0 : ℝ)..1,
      r * Real.rpow
        (1 - Real.rpow r n) (alpha + 1 / n)
  have hpow : Continuous
      (fun p : ℝ × ℝ =>
        Real.rpow
          (baseResidual a b n p.1 p.2) alpha) :=
    (Real.continuous_rpow_const halpha).comp
      (baseResidual_continuous a b n hn)
  have hf : Continuous
      (fun p : ℝ × ℝ =>
        p.1 *
          Real.rpow
            (baseResidual a b n p.1 p.2) alpha) :=
    continuous_fst.mul hpow
  have hiter :=
    base_integral_as_iterated a b n ha hb hn _ hf
  have hinner :
      (∫ x in (0 : ℝ)..a,
          ∫ y in (0 : ℝ)..ordinateBound a b n x,
            x * Real.rpow
              (baseResidual a b n x y) alpha) =
        ∫ x in (0 : ℝ)..a,
          (b * J₀) *
            (x * Real.rpow (residual a n x)
              (alpha + 1 / n)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) a := by
      simpa [Set.uIcc_of_le ha.le] using hx
    calc
      (∫ y in (0 : ℝ)..ordinateBound a b n x,
          x * Real.rpow
            (baseResidual a b n x y) alpha) =
        x * ∫ y in (0 : ℝ)..ordinateBound a b n x,
          Real.rpow
            (baseResidual a b n x y) alpha := by
        rw [intervalIntegral.integral_const_mul]
      _ = x *
          (b * Real.rpow (residual a n x)
            (alpha + 1 / n) * J₀) := by
        rw [inner_power_integral
          a b n alpha x ha hb hn halpha hx']
      _ = _ := by ring
  have hpull :
      (∫ x in (0 : ℝ)..a,
          (b * J₀) *
            (x * Real.rpow (residual a n x)
              (alpha + 1 / n))) =
        (b * J₀) *
          ∫ x in (0 : ℝ)..a,
            x * Real.rpow (residual a n x)
              (alpha + 1 / n) := by
    rw [intervalIntegral.integral_const_mul]
  have houter :
      (∫ x in (0 : ℝ)..a,
          x * Real.rpow (residual a n x)
            (alpha + 1 / n)) =
        a ^ 2 * K₁ := by
    have hscale :
        a *
            (∫ r in (0 : ℝ)..1,
              (a * r) *
                Real.rpow
                  (residual a n (a * r))
                  (alpha + 1 / n)) =
          ∫ x in (0 : ℝ)..a,
            x * Real.rpow (residual a n x)
              (alpha + 1 / n) := by
      simpa only [mul_zero, mul_one] using
        (intervalIntegral.mul_integral_comp_mul_left
          (f := fun x =>
            x * Real.rpow (residual a n x)
              (alpha + 1 / n))
          (a := (0 : ℝ)) (b := 1) a)
    rw [← hscale]
    calc
      a *
          (∫ r in (0 : ℝ)..1,
            (a * r) *
              Real.rpow (residual a n (a * r))
                (alpha + 1 / n)) =
        a *
          (∫ r in (0 : ℝ)..1,
            a *
              (r * Real.rpow
                (1 - Real.rpow r n)
                (alpha + 1 / n))) := by
        apply congrArg (fun z : ℝ => a * z)
        apply intervalIntegral.integral_congr
        intro r hr
        dsimp only
        rw [residual_scale a n r ha]
        ring
      _ = a * (a * K₁) := by
        rw [intervalIntegral.integral_const_mul]
      _ = a ^ 2 * K₁ := by ring
  rw [hiter, hinner, hpull, houter]
  dsimp [J₀, K₁]
  ring

private theorem base_y_power_factorization
    (a b n alpha : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (halpha : 0 ≤ alpha) :
    (∫ p in baseRegion a b n,
        p.2 *
          Real.rpow
            (baseResidual a b n p.1 p.2) alpha) =
      a * b ^ 2 *
        (∫ r in (0 : ℝ)..1,
          Real.rpow
            (1 - Real.rpow r n) (alpha + 2 / n)) *
        (∫ t in (0 : ℝ)..1,
          t * Real.rpow (1 - Real.rpow t n) alpha) := by
  let K₀ : ℝ :=
    ∫ t in (0 : ℝ)..1,
      t * Real.rpow (1 - Real.rpow t n) alpha
  let J₂ : ℝ :=
    ∫ r in (0 : ℝ)..1,
      Real.rpow
        (1 - Real.rpow r n) (alpha + 2 / n)
  have hpow : Continuous
      (fun p : ℝ × ℝ =>
        Real.rpow
          (baseResidual a b n p.1 p.2) alpha) :=
    (Real.continuous_rpow_const halpha).comp
      (baseResidual_continuous a b n hn)
  have hf : Continuous
      (fun p : ℝ × ℝ =>
        p.2 *
          Real.rpow
            (baseResidual a b n p.1 p.2) alpha) :=
    continuous_snd.mul hpow
  have hiter :=
    base_integral_as_iterated a b n ha hb hn _ hf
  have hinner :
      (∫ x in (0 : ℝ)..a,
          ∫ y in (0 : ℝ)..ordinateBound a b n x,
            y * Real.rpow
              (baseResidual a b n x y) alpha) =
        ∫ x in (0 : ℝ)..a,
          (b ^ 2 * K₀) *
            Real.rpow (residual a n x)
              (alpha + 2 / n) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) a := by
      simpa [Set.uIcc_of_le ha.le] using hx
    dsimp only
    rw [inner_first_moment_integral
      a b n alpha x ha hb hn halpha hx']
    ring
  have hpull :
      (∫ x in (0 : ℝ)..a,
          (b ^ 2 * K₀) *
            Real.rpow (residual a n x)
              (alpha + 2 / n)) =
        (b ^ 2 * K₀) *
          ∫ x in (0 : ℝ)..a,
            Real.rpow (residual a n x)
              (alpha + 2 / n) := by
    rw [intervalIntegral.integral_const_mul]
  have houter :
      (∫ x in (0 : ℝ)..a,
          Real.rpow (residual a n x)
            (alpha + 2 / n)) =
        a * J₂ := by
    have hscale :
        a *
            (∫ r in (0 : ℝ)..1,
              Real.rpow
                (residual a n (a * r))
                (alpha + 2 / n)) =
          ∫ x in (0 : ℝ)..a,
            Real.rpow (residual a n x)
              (alpha + 2 / n) := by
      simpa only [mul_zero, mul_one] using
        (intervalIntegral.mul_integral_comp_mul_left
          (f := fun x =>
            Real.rpow (residual a n x)
              (alpha + 2 / n))
          (a := (0 : ℝ)) (b := 1) a)
    rw [← hscale]
    apply congrArg (fun z : ℝ => a * z)
    dsimp [J₂]
    apply intervalIntegral.integral_congr
    intro r hr
    dsimp only
    change
      Real.rpow (residual a n (a * r))
          (alpha + 2 / n) =
        Real.rpow (1 - Real.rpow r n)
          (alpha + 2 / n)
    rw [residual_scale a n r ha]
  rw [hiter, hinner, hpull, houter]
  dsimp [K₀, J₂]
  ring

private theorem solid_closed
    (a b c n : ℝ) (hn : 0 < n) :
    IsClosed (solid a b c n) := by
  have hx :
      Continuous (fun p : Point3 =>
        Real.rpow (p.1 / a) n) :=
    (Real.continuous_rpow_const hn.le).comp
      (continuous_fst.div_const a)
  have hy :
      Continuous (fun p : Point3 =>
        Real.rpow (p.2.1 / b) n) :=
    (Real.continuous_rpow_const hn.le).comp
      ((continuous_fst.comp continuous_snd).div_const b)
  have hz :
      Continuous (fun p : Point3 =>
        Real.rpow (p.2.2 / c) n) :=
    (Real.continuous_rpow_const hn.le).comp
      ((continuous_snd.comp continuous_snd).div_const c)
  unfold solid
  exact
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const
        (continuous_fst.comp continuous_snd)).inter
      ((isClosed_le continuous_const
        (continuous_snd.comp continuous_snd)).inter
      (isClosed_le ((hx.add hy).add hz) continuous_const)))

private theorem solid_compact
    (a b c n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : 0 < n) :
    IsCompact (solid a b c n) := by
  apply
    (isCompact_Icc :
      IsCompact
        (Set.Icc
          ((0 : ℝ), ((0 : ℝ), (0 : ℝ)))
          (a, (b, c)))).of_isClosed_subset
      (solid_closed a b c n hn)
  rintro ⟨x, y, z⟩ hp
  change
    0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧
      Real.rpow (x / a) n +
        Real.rpow (y / b) n +
        Real.rpow (z / c) n ≤ 1 at hp
  have hxratio : 0 ≤ x / a := div_nonneg hp.1 ha.le
  have hyratio : 0 ≤ y / b := div_nonneg hp.2.1 hb.le
  have hzratio : 0 ≤ z / c := div_nonneg hp.2.2.1 hc.le
  have hxpow0 : 0 ≤ Real.rpow (x / a) n :=
    Real.rpow_nonneg hxratio n
  have hypow0 : 0 ≤ Real.rpow (y / b) n :=
    Real.rpow_nonneg hyratio n
  have hzpow0 : 0 ≤ Real.rpow (z / c) n :=
    Real.rpow_nonneg hzratio n
  have hxpow1 : Real.rpow (x / a) n ≤ 1 := by linarith
  have hypow1 : Real.rpow (y / b) n ≤ 1 := by linarith
  have hzpow1 : Real.rpow (z / c) n ≤ 1 := by linarith
  have hxratio1 : x / a ≤ 1 :=
    (Real.rpow_le_rpow_iff hxratio zero_le_one hn).mp
      (by simpa only [Real.one_rpow] using hxpow1)
  have hyratio1 : y / b ≤ 1 :=
    (Real.rpow_le_rpow_iff hyratio zero_le_one hn).mp
      (by simpa only [Real.one_rpow] using hypow1)
  have hzratio1 : z / c ≤ 1 :=
    (Real.rpow_le_rpow_iff hzratio zero_le_one hn).mp
      (by simpa only [Real.one_rpow] using hzpow1)
  exact
    ⟨⟨hp.1, hp.2.1, hp.2.2.1⟩,
      ⟨(div_le_one ha).mp hxratio1,
        (div_le_one hb).mp hyratio1,
        (div_le_one hc).mp hzratio1⟩⟩

private theorem solid_indicator_integrable
    (a b c n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : 0 < n) (f : Point3 → ℝ)
    (hf : Continuous f) :
    Integrable ((solid a b c n).indicator f) := by
  rw [integrable_indicator_iff
    (solid_closed a b c n hn).measurableSet]
  exact hf.continuousOn.integrableOn_compact
    (solid_compact a b c n ha hb hc hn)

private theorem baseResidual_nonneg_of_mem
    (a b n x y : ℝ)
    (hp : (x, y) ∈ baseRegion a b n) :
    0 ≤ baseResidual a b n x y := by
  change
    0 ≤ x ∧ 0 ≤ y ∧
      Real.rpow (x / a) n +
        Real.rpow (y / b) n ≤ 1 at hp
  unfold baseResidual
  linarith

private theorem capHeight_nonneg
    (a b c n x y : ℝ) (hc : 0 < c)
    (hp : (x, y) ∈ baseRegion a b n) :
    0 ≤ capHeight a b c n x y := by
  unfold capHeight
  exact mul_nonneg hc.le
    (Real.rpow_nonneg
      (baseResidual_nonneg_of_mem a b n x y hp) _)

private theorem solid_base_mem
    (a b c n x y z : ℝ)
    (hc : 0 < c)
    (hp : (x, y, z) ∈ solid a b c n) :
    (x, y) ∈ baseRegion a b n := by
  change
    0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧
      Real.rpow (x / a) n +
        Real.rpow (y / b) n +
        Real.rpow (z / c) n ≤ 1 at hp
  change
    0 ≤ x ∧ 0 ≤ y ∧
      Real.rpow (x / a) n +
        Real.rpow (y / b) n ≤ 1
  have hzpow0 :
      0 ≤ Real.rpow (z / c) n :=
    Real.rpow_nonneg (div_nonneg hp.2.2.1 hc.le) _
  exact ⟨hp.1, hp.2.1, by linarith⟩

private theorem solid_section_iff
    (a b c n x y z : ℝ)
    (hc : 0 < c) (hn : 0 < n)
    (hbase : (x, y) ∈ baseRegion a b n) :
    (x, y, z) ∈ solid a b c n ↔
      z ∈ Set.Icc (0 : ℝ)
        (capHeight a b c n x y) := by
  let L : ℝ := baseResidual a b n x y
  let q : ℝ := Real.rpow L (1 / n)
  have hL : 0 ≤ L :=
    baseResidual_nonneg_of_mem a b n x y hbase
  have hq : 0 ≤ q := Real.rpow_nonneg hL _
  have hqn : Real.rpow q n = L := by
    dsimp [q]
    exact rpow_one_div_rpow L n hn hL
  have hqnPow : q ^ n = L := by
    simpa only [← Real.rpow_eq_pow] using hqn
  change
    0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧
        Real.rpow (x / a) n +
          Real.rpow (y / b) n +
          Real.rpow (z / c) n ≤ 1 ↔
      0 ≤ z ∧ z ≤ capHeight a b c n x y
  change
    0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧
        Real.rpow (x / a) n +
          Real.rpow (y / b) n +
          Real.rpow (z / c) n ≤ 1 ↔
      0 ≤ z ∧ z ≤ c * q
  constructor
  · intro hp
    have hzratio0 : 0 ≤ z / c :=
      div_nonneg hp.2.2.1 hc.le
    have hzpowle :
        (z / c) ^ n ≤ L := by
      dsimp [L, baseResidual]
      simpa only [Real.rpow_eq_pow] using
        (show
          Real.rpow (z / c) n ≤
            1 -
              (Real.rpow (x / a) n +
                Real.rpow (y / b) n) by
          linarith)
    have hzratioq : z / c ≤ q := by
      apply
        (Real.rpow_le_rpow_iff hzratio0 hq hn).mp
      rw [hqnPow]
      exact hzpowle
    refine ⟨hp.2.2.1, ?_⟩
    simpa [mul_comm] using (div_le_iff₀ hc).mp hzratioq
  · intro hz
    have hzratio0 : 0 ≤ z / c :=
      div_nonneg hz.1 hc.le
    have hzratioq : z / c ≤ q := by
      apply (div_le_iff₀ hc).mpr
      simpa [mul_comm] using hz.2
    have hzpowle : (z / c) ^ n ≤ L := by
      have hp :=
        (Real.rpow_le_rpow_iff hzratio0 hq hn).mpr
          hzratioq
      rwa [hqnPow] at hp
    change
      0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧
        Real.rpow (x / a) n +
          Real.rpow (y / b) n +
          Real.rpow (z / c) n ≤ 1
    change
      0 ≤ x ∧ 0 ≤ y ∧
        Real.rpow (x / a) n +
          Real.rpow (y / b) n ≤ 1 at hbase
    refine ⟨hbase.1, hbase.2.1, hz.1, ?_⟩
    dsimp [L, baseResidual] at hzpowle
    simp only [Real.rpow_eq_pow]
    linarith

private theorem solid_integral_as_base
    (a b c n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : 0 < n) (f : Point3 → ℝ)
    (hf : Continuous f) :
    (∫ p in solid a b c n, f p) =
      ∫ q in baseRegion a b n,
        ∫ z in (0 : ℝ)..capHeight a b c n q.1 q.2,
          f (q.1, q.2, z) := by
  let e :=
    (MeasurableEquiv.prodAssoc :
      ((ℝ × ℝ) × ℝ) ≃ᵐ Point3)
  have hfi : Integrable
      ((solid a b c n).indicator f) :=
    solid_indicator_integrable
      a b c n ha hb hc hn f hf
  have hfi' : Integrable
      (fun q : (ℝ × ℝ) × ℝ =>
        (solid a b c n).indicator f (e q)) := by
    simpa only [Function.comp_apply] using
      (volume_preserving_prodAssoc.integrable_comp_emb
        e.measurableEmbedding).2 hfi
  have hreassoc :
      (∫ q : (ℝ × ℝ) × ℝ,
          (solid a b c n).indicator f (e q)) =
        ∫ p : Point3,
          (solid a b c n).indicator f p :=
    volume_preserving_prodAssoc.integral_comp'
      ((solid a b c n).indicator f)
  rw [← integral_indicator
    (solid_closed a b c n hn).measurableSet]
  rw [← hreassoc]
  have hFubini :
      (∫ q : (ℝ × ℝ) × ℝ,
          (solid a b c n).indicator f (e q)) =
        ∫ q : ℝ × ℝ, ∫ z : ℝ,
          (solid a b c n).indicator f (e (q, z)) := by
    exact MeasureTheory.integral_prod
      (fun q : (ℝ × ℝ) × ℝ =>
        (solid a b c n).indicator f (e q)) hfi'
  rw [hFubini]
  change
    (∫ q : ℝ × ℝ, ∫ z : ℝ,
      (solid a b c n).indicator f
        (q.1, q.2, z)) =
      ∫ q in baseRegion a b n,
        ∫ z in (0 : ℝ)..capHeight a b c n q.1 q.2,
          f (q.1, q.2, z)
  have hsection (q : ℝ × ℝ) :
      (∫ z : ℝ,
        (solid a b c n).indicator f
          (q.1, q.2, z)) =
        (baseRegion a b n).indicator
          (fun q =>
            ∫ z in (0 : ℝ)..
                capHeight a b c n q.1 q.2,
              f (q.1, q.2, z)) q := by
    by_cases hq : q ∈ baseRegion a b n
    · have hmem (z : ℝ) :
          (q.1, q.2, z) ∈ solid a b c n ↔
            z ∈ Set.Icc (0 : ℝ)
              (capHeight a b c n q.1 q.2) :=
        solid_section_iff
          a b c n q.1 q.2 z hc hn hq
      have hfun :
          (fun z : ℝ =>
            (solid a b c n).indicator f
              (q.1, q.2, z)) =
            (Set.Icc (0 : ℝ)
              (capHeight a b c n q.1 q.2)).indicator
              (fun z => f (q.1, q.2, z)) := by
        funext z
        by_cases hz :
            z ∈ Set.Icc (0 : ℝ)
              (capHeight a b c n q.1 q.2)
        · have hp := (hmem z).mpr hz
          rw [Set.indicator_of_mem hp,
            Set.indicator_of_mem hz]
        · have hp : (q.1, q.2, z) ∉
              solid a b c n := by
            exact fun h => hz ((hmem z).mp h)
          rw [Set.indicator_of_notMem hp,
            Set.indicator_of_notMem hz]
      rw [hfun,
        MeasureTheory.integral_indicator measurableSet_Icc,
        integral_Icc_eq_integral_Ioc]
      rw [← intervalIntegral.integral_of_le
        (capHeight_nonneg
          a b c n q.1 q.2 hc hq)]
      rw [Set.indicator_of_mem hq]
    · have hnone (z : ℝ) :
          (q.1, q.2, z) ∉ solid a b c n := by
        intro hp
        exact hq
          (solid_base_mem
            a b c n q.1 q.2 z hc hp)
      simp [Set.indicator, hnone, hq]
  simp_rw [hsection]
  rw [integral_indicator
    (baseRegion_closed a b n hn).measurableSet]

private theorem mass_factorization
    (a b c n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : 0 < n) :
    mass a b c n =
      a * b * c *
        (∫ r in (0 : ℝ)..1,
          Real.rpow (1 - Real.rpow r n) (2 / n)) *
        (∫ t in (0 : ℝ)..1,
          Real.rpow (1 - Real.rpow t n) (1 / n)) := by
  unfold mass
  rw [solid_integral_as_base
    a b c n ha hb hc hn
    (fun _p : Point3 => (1 : ℝ)) continuous_const]
  calc
    (∫ q in baseRegion a b n,
        ∫ z in (0 : ℝ)..capHeight a b c n q.1 q.2,
          (1 : ℝ)) =
        ∫ q in baseRegion a b n,
          capHeight a b c n q.1 q.2 := by
      apply MeasureTheory.setIntegral_congr_fun
        (baseRegion_closed a b n hn).measurableSet
      intro q hq
      dsimp only
      rw [intervalIntegral.integral_const]
      simp
    _ = c *
        ∫ q in baseRegion a b n,
          Real.rpow
            (baseResidual a b n q.1 q.2) (1 / n) := by
      unfold capHeight
      rw [MeasureTheory.integral_const_mul]
    _ = _ := by
      rw [base_power_factorization
        a b n (1 / n) ha hb hn
        (one_div_pos.mpr hn).le]
      ring

private theorem xMoment_factorization
    (a b c n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : 0 < n) :
    (∫ p in solid a b c n, p.1) =
      a ^ 2 * b * c *
        (∫ r in (0 : ℝ)..1,
          r * Real.rpow
            (1 - Real.rpow r n) (2 / n)) *
        (∫ t in (0 : ℝ)..1,
          Real.rpow (1 - Real.rpow t n) (1 / n)) := by
  rw [solid_integral_as_base
    a b c n ha hb hc hn
    (fun p : Point3 => p.1) continuous_fst]
  calc
    (∫ q in baseRegion a b n,
        ∫ z in (0 : ℝ)..capHeight a b c n q.1 q.2,
          q.1) =
        ∫ q in baseRegion a b n,
          q.1 * capHeight a b c n q.1 q.2 := by
      apply MeasureTheory.setIntegral_congr_fun
        (baseRegion_closed a b n hn).measurableSet
      intro q hq
      dsimp only
      rw [intervalIntegral.integral_const]
      simp
      ring
    _ = c *
        ∫ q in baseRegion a b n,
          q.1 *
            Real.rpow
              (baseResidual a b n q.1 q.2) (1 / n) := by
      unfold capHeight
      calc
        (∫ q in baseRegion a b n,
            q.1 *
              (c * Real.rpow
                (baseResidual a b n q.1 q.2) (1 / n))) =
            ∫ q in baseRegion a b n,
              c * (q.1 *
                Real.rpow
                  (baseResidual a b n q.1 q.2)
                  (1 / n)) := by
          apply MeasureTheory.setIntegral_congr_fun
            (baseRegion_closed a b n hn).measurableSet
          intro q hq
          ring
        _ = _ := by
          rw [MeasureTheory.integral_const_mul]
    _ = _ := by
      rw [base_x_power_factorization
        a b n (1 / n) ha hb hn
        (one_div_pos.mpr hn).le]
      ring

private theorem yMoment_factorization
    (a b c n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : 0 < n) :
    (∫ p in solid a b c n, p.2.1) =
      a * b ^ 2 * c *
        (∫ r in (0 : ℝ)..1,
          Real.rpow
            (1 - Real.rpow r n) (3 / n)) *
        (∫ t in (0 : ℝ)..1,
          t * Real.rpow (1 - Real.rpow t n) (1 / n)) := by
  rw [solid_integral_as_base
    a b c n ha hb hc hn
    (fun p : Point3 => p.2.1)
    (continuous_fst.comp continuous_snd)]
  calc
    (∫ q in baseRegion a b n,
        ∫ z in (0 : ℝ)..capHeight a b c n q.1 q.2,
          q.2) =
        ∫ q in baseRegion a b n,
          q.2 * capHeight a b c n q.1 q.2 := by
      apply MeasureTheory.setIntegral_congr_fun
        (baseRegion_closed a b n hn).measurableSet
      intro q hq
      dsimp only
      rw [intervalIntegral.integral_const]
      simp
      ring
    _ = c *
        ∫ q in baseRegion a b n,
          q.2 *
            Real.rpow
              (baseResidual a b n q.1 q.2) (1 / n) := by
      unfold capHeight
      calc
        (∫ q in baseRegion a b n,
            q.2 *
              (c * Real.rpow
                (baseResidual a b n q.1 q.2) (1 / n))) =
            ∫ q in baseRegion a b n,
              c * (q.2 *
                Real.rpow
                  (baseResidual a b n q.1 q.2)
                  (1 / n)) := by
          apply MeasureTheory.setIntegral_congr_fun
            (baseRegion_closed a b n hn).measurableSet
          intro q hq
          ring
        _ = _ := by
          rw [MeasureTheory.integral_const_mul]
    _ = _ := by
      rw [base_y_power_factorization
        a b n (1 / n) ha hb hn
        (one_div_pos.mpr hn).le]
      ring

private theorem zMoment_factorization
    (a b c n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : 0 < n) :
    (∫ p in solid a b c n, p.2.2) =
      a * b * c ^ 2 / 2 *
        (∫ r in (0 : ℝ)..1,
          Real.rpow (1 - Real.rpow r n) (3 / n)) *
        (∫ t in (0 : ℝ)..1,
          Real.rpow (1 - Real.rpow t n) (2 / n)) := by
  rw [solid_integral_as_base
    a b c n ha hb hc hn
    (fun p : Point3 => p.2.2)
    (continuous_snd.comp continuous_snd)]
  calc
    (∫ q in baseRegion a b n,
        ∫ z in (0 : ℝ)..capHeight a b c n q.1 q.2,
          z) =
        ∫ q in baseRegion a b n,
          capHeight a b c n q.1 q.2 ^ 2 / 2 := by
      apply MeasureTheory.setIntegral_congr_fun
        (baseRegion_closed a b n hn).measurableSet
      intro q hq
      dsimp only
      rw [integral_id]
      ring
    _ = (c ^ 2 / 2) *
        ∫ q in baseRegion a b n,
          Real.rpow
            (baseResidual a b n q.1 q.2) (2 / n) := by
      calc
        (∫ q in baseRegion a b n,
            capHeight a b c n q.1 q.2 ^ 2 / 2) =
          ∫ q in baseRegion a b n,
            (c ^ 2 / 2) *
              Real.rpow
                (baseResidual a b n q.1 q.2)
                (2 / n) := by
          apply MeasureTheory.setIntegral_congr_fun
            (baseRegion_closed a b n hn).measurableSet
          intro q hq
          have hL :
              0 ≤ baseResidual a b n q.1 q.2 :=
            baseResidual_nonneg_of_mem
              a b n q.1 q.2 hq
          have hexp : 0 ≤ 1 / n :=
            (one_div_pos.mpr hn).le
          have hq2 :
              Real.rpow
                  (baseResidual a b n q.1 q.2)
                  (1 / n) ^ 2 =
                Real.rpow
                  (baseResidual a b n q.1 q.2)
                  (2 / n) := by
            calc
              Real.rpow
                    (baseResidual a b n q.1 q.2)
                    (1 / n) ^ 2 =
                  Real.rpow
                      (baseResidual a b n q.1 q.2)
                      (1 / n) *
                    Real.rpow
                      (baseResidual a b n q.1 q.2)
                      (1 / n) := by ring
              _ = Real.rpow
                    (baseResidual a b n q.1 q.2)
                    (1 / n + 1 / n) :=
                (Real.rpow_add_of_nonneg
                  hL hexp hexp).symm
              _ = Real.rpow
                    (baseResidual a b n q.1 q.2)
                    (2 / n) := by
                congr 1
                field_simp [hn.ne']
                ring
          dsimp only
          unfold capHeight
          rw [mul_pow, hq2]
          ring
        _ = _ := by
          rw [MeasureTheory.integral_const_mul]
    _ = _ := by
      rw [base_power_factorization
        a b n (2 / n) ha hb hn
        (div_nonneg (by norm_num) hn.le)]
      ring

private theorem beta_mass_product_value
    (n : ℝ) (hn : 0 < n) :
    betaFn (2 / n + 1) (1 / n) *
        betaFn (1 / n + 1) (1 / n) =
      Real.Gamma (1 / n) ^ 3 /
        (3 * Real.Gamma (3 / n)) := by
  have hpos1 : 0 < 1 / n := one_div_pos.mpr hn
  have hpos2 : 0 < 2 / n := div_pos (by norm_num) hn
  have hpos3 : 0 < 3 / n := div_pos (by norm_num) hn
  rw [betaFn_eq_Gamma_mul_div
      (2 / n + 1) (1 / n) (by positivity) hpos1,
    betaFn_eq_Gamma_mul_div
      (1 / n + 1) (1 / n) (by positivity) hpos1]
  have hsum3 :
      2 / n + 1 + 1 / n = 3 / n + 1 := by
    field_simp [hn.ne']
    ring
  have hsum2 :
      1 / n + 1 + 1 / n = 2 / n + 1 := by
    field_simp [hn.ne']
    ring
  rw [hsum3, hsum2,
    Real.Gamma_add_one hpos1.ne',
    Real.Gamma_add_one hpos2.ne',
    Real.Gamma_add_one hpos3.ne']
  have hgamma2 :
      Real.Gamma (2 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos hpos2).ne'
  have hgamma3 :
      Real.Gamma (3 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos hpos3).ne'
  field_simp [hn.ne', hgamma2, hgamma3]

private theorem beta_x_product_value
    (n : ℝ) (hn : 0 < n) :
    betaFn (2 / n + 1) (2 / n) *
        betaFn (1 / n + 1) (1 / n) =
      Real.Gamma (1 / n) ^ 2 *
          Real.Gamma (2 / n) /
        (4 * Real.Gamma (4 / n)) := by
  have hpos1 : 0 < 1 / n := one_div_pos.mpr hn
  have hpos2 : 0 < 2 / n := div_pos (by norm_num) hn
  have hpos4 : 0 < 4 / n := div_pos (by norm_num) hn
  rw [betaFn_eq_Gamma_mul_div
      (2 / n + 1) (2 / n) (by positivity) hpos2,
    betaFn_eq_Gamma_mul_div
      (1 / n + 1) (1 / n) (by positivity) hpos1]
  have hsum4 :
      2 / n + 1 + 2 / n = 4 / n + 1 := by
    field_simp [hn.ne']
    ring
  have hsum2 :
      1 / n + 1 + 1 / n = 2 / n + 1 := by
    field_simp [hn.ne']
    ring
  rw [hsum4, hsum2,
    Real.Gamma_add_one hpos1.ne',
    Real.Gamma_add_one hpos2.ne',
    Real.Gamma_add_one hpos4.ne']
  have hgamma1 :
      Real.Gamma (1 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos hpos1).ne'
  have hgamma2 :
      Real.Gamma (2 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos hpos2).ne'
  have hgamma4 :
      Real.Gamma (4 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos hpos4).ne'
  field_simp [hn.ne', hgamma1, hgamma2, hgamma4]

private theorem beta_y_product_value
    (n : ℝ) (hn : 0 < n) :
    betaFn (3 / n + 1) (1 / n) *
        betaFn (1 / n + 1) (2 / n) =
      Real.Gamma (1 / n) ^ 2 *
          Real.Gamma (2 / n) /
        (4 * Real.Gamma (4 / n)) := by
  have hpos1 : 0 < 1 / n := one_div_pos.mpr hn
  have hpos2 : 0 < 2 / n := div_pos (by norm_num) hn
  have hpos3 : 0 < 3 / n := div_pos (by norm_num) hn
  have hpos4 : 0 < 4 / n := div_pos (by norm_num) hn
  rw [betaFn_eq_Gamma_mul_div
      (3 / n + 1) (1 / n) (by positivity) hpos1,
    betaFn_eq_Gamma_mul_div
      (1 / n + 1) (2 / n) (by positivity) hpos2]
  have hsum4 :
      3 / n + 1 + 1 / n = 4 / n + 1 := by
    field_simp [hn.ne']
    ring
  have hsum3 :
      1 / n + 1 + 2 / n = 3 / n + 1 := by
    field_simp [hn.ne']
    ring
  rw [hsum4, hsum3,
    Real.Gamma_add_one hpos1.ne',
    Real.Gamma_add_one hpos3.ne',
    Real.Gamma_add_one hpos4.ne']
  have hgamma1 :
      Real.Gamma (1 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos hpos1).ne'
  have hgamma2 :
      Real.Gamma (2 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos hpos2).ne'
  have hgamma3 :
      Real.Gamma (3 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos hpos3).ne'
  have hgamma4 :
      Real.Gamma (4 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos hpos4).ne'
  field_simp [hn.ne', hgamma1, hgamma2, hgamma3,
    hgamma4]

private theorem beta_z_product_value
    (n : ℝ) (hn : 0 < n) :
    betaFn (3 / n + 1) (1 / n) *
        betaFn (2 / n + 1) (1 / n) =
      Real.Gamma (1 / n) ^ 2 *
          Real.Gamma (2 / n) /
        (2 * Real.Gamma (4 / n)) := by
  have hpos1 : 0 < 1 / n := one_div_pos.mpr hn
  have hpos2 : 0 < 2 / n := div_pos (by norm_num) hn
  have hpos3 : 0 < 3 / n := div_pos (by norm_num) hn
  have hpos4 : 0 < 4 / n := div_pos (by norm_num) hn
  rw [betaFn_eq_Gamma_mul_div
      (3 / n + 1) (1 / n) (by positivity) hpos1,
    betaFn_eq_Gamma_mul_div
      (2 / n + 1) (1 / n) (by positivity) hpos1]
  have hsum4 :
      3 / n + 1 + 1 / n = 4 / n + 1 := by
    field_simp [hn.ne']
    ring
  have hsum3 :
      2 / n + 1 + 1 / n = 3 / n + 1 := by
    field_simp [hn.ne']
    ring
  rw [hsum4, hsum3,
    Real.Gamma_add_one hpos2.ne',
    Real.Gamma_add_one hpos3.ne',
    Real.Gamma_add_one hpos4.ne']
  have hgamma1 :
      Real.Gamma (1 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos hpos1).ne'
  have hgamma2 :
      Real.Gamma (2 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos hpos2).ne'
  have hgamma3 :
      Real.Gamma (3 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos hpos3).ne'
  have hgamma4 :
      Real.Gamma (4 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos hpos4).ne'
  field_simp [hn.ne', hgamma1, hgamma2, hgamma3,
    hgamma4]
  ring

private theorem mass_formula
    (a b c n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : 0 < n) :
    mass a b c n =
      a * b * c / (3 * n ^ 2) *
        (Real.Gamma (1 / n) ^ 3 /
          Real.Gamma (3 / n)) := by
  rw [mass_factorization a b c n ha hb hc hn,
    unit_rpow_integral n (2 / n) hn,
    unit_rpow_integral n (1 / n) hn]
  calc
    a * b * c *
          (1 / n * betaFn (2 / n + 1) (1 / n)) *
          (1 / n * betaFn (1 / n + 1) (1 / n)) =
        a * b * c * (1 / n) ^ 2 *
          (betaFn (2 / n + 1) (1 / n) *
            betaFn (1 / n + 1) (1 / n)) := by
      ring
    _ = a * b * c * (1 / n) ^ 2 *
          (Real.Gamma (1 / n) ^ 3 /
            (3 * Real.Gamma (3 / n))) := by
      rw [beta_mass_product_value n hn]
    _ = _ := by
      field_simp [hn.ne']

private theorem xMoment_formula
    (a b c n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : 0 < n) :
    (∫ p in solid a b c n, p.1) =
      a ^ 2 * b * c / (4 * n ^ 2) *
        (Real.Gamma (1 / n) ^ 2 *
            Real.Gamma (2 / n) /
          Real.Gamma (4 / n)) := by
  rw [xMoment_factorization a b c n ha hb hc hn,
    unit_rpow_first_moment_integral n (2 / n) hn,
    unit_rpow_integral n (1 / n) hn]
  calc
    a ^ 2 * b * c *
          (1 / n * betaFn (2 / n + 1) (2 / n)) *
          (1 / n * betaFn (1 / n + 1) (1 / n)) =
        a ^ 2 * b * c * (1 / n) ^ 2 *
          (betaFn (2 / n + 1) (2 / n) *
            betaFn (1 / n + 1) (1 / n)) := by
      ring
    _ = a ^ 2 * b * c * (1 / n) ^ 2 *
          (Real.Gamma (1 / n) ^ 2 *
              Real.Gamma (2 / n) /
            (4 * Real.Gamma (4 / n))) := by
      rw [beta_x_product_value n hn]
    _ = _ := by
      field_simp [hn.ne']

private theorem yMoment_formula
    (a b c n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : 0 < n) :
    (∫ p in solid a b c n, p.2.1) =
      a * b ^ 2 * c / (4 * n ^ 2) *
        (Real.Gamma (1 / n) ^ 2 *
            Real.Gamma (2 / n) /
          Real.Gamma (4 / n)) := by
  rw [yMoment_factorization a b c n ha hb hc hn,
    unit_rpow_integral n (3 / n) hn,
    unit_rpow_first_moment_integral n (1 / n) hn]
  calc
    a * b ^ 2 * c *
          (1 / n * betaFn (3 / n + 1) (1 / n)) *
          (1 / n * betaFn (1 / n + 1) (2 / n)) =
        a * b ^ 2 * c * (1 / n) ^ 2 *
          (betaFn (3 / n + 1) (1 / n) *
            betaFn (1 / n + 1) (2 / n)) := by
      ring
    _ = a * b ^ 2 * c * (1 / n) ^ 2 *
          (Real.Gamma (1 / n) ^ 2 *
              Real.Gamma (2 / n) /
            (4 * Real.Gamma (4 / n))) := by
      rw [beta_y_product_value n hn]
    _ = _ := by
      field_simp [hn.ne']

private theorem zMoment_formula
    (a b c n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : 0 < n) :
    (∫ p in solid a b c n, p.2.2) =
      a * b * c ^ 2 / (4 * n ^ 2) *
        (Real.Gamma (1 / n) ^ 2 *
            Real.Gamma (2 / n) /
          Real.Gamma (4 / n)) := by
  rw [zMoment_factorization a b c n ha hb hc hn,
    unit_rpow_integral n (3 / n) hn,
    unit_rpow_integral n (2 / n) hn]
  calc
    a * b * c ^ 2 / 2 *
          (1 / n * betaFn (3 / n + 1) (1 / n)) *
          (1 / n * betaFn (2 / n + 1) (1 / n)) =
        a * b * c ^ 2 / 2 * (1 / n) ^ 2 *
          (betaFn (3 / n + 1) (1 / n) *
            betaFn (2 / n + 1) (1 / n)) := by
      ring
    _ = a * b * c ^ 2 / 2 * (1 / n) ^ 2 *
          (Real.Gamma (1 / n) ^ 2 *
              Real.Gamma (2 / n) /
            (2 * Real.Gamma (4 / n))) := by
      rw [beta_z_product_value n hn]
    _ = _ := by
      field_simp [hn.ne']
      norm_num

private theorem mass_pos
    (a b c n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : 0 < n) :
    0 < mass a b c n := by
  rw [mass_formula a b c n ha hb hc hn]
  have hpos1 : 0 < 1 / n := one_div_pos.mpr hn
  have hpos3 : 0 < 3 / n := div_pos (by norm_num) hn
  have hg1 : 0 < Real.Gamma (1 / n) :=
    Real.Gamma_pos_of_pos hpos1
  have hg3 : 0 < Real.Gamma (3 / n) :=
    Real.Gamma_pos_of_pos hpos3
  positivity

private theorem xCentroid_formula
    (a b c n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : 0 < n) :
    (∫ p in solid a b c n, p.1) / mass a b c n =
      centroidFactor n * a := by
  rw [xMoment_formula a b c n ha hb hc hn,
    mass_formula a b c n ha hb hc hn]
  unfold centroidFactor
  have hpos1 : 0 < 1 / n := one_div_pos.mpr hn
  have hpos2 : 0 < 2 / n := div_pos (by norm_num) hn
  have hpos3 : 0 < 3 / n := div_pos (by norm_num) hn
  have hpos4 : 0 < 4 / n := div_pos (by norm_num) hn
  have hg1 : Real.Gamma (1 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos hpos1).ne'
  have hg2 : Real.Gamma (2 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos hpos2).ne'
  have hg3 : Real.Gamma (3 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos hpos3).ne'
  have hg4 : Real.Gamma (4 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos hpos4).ne'
  field_simp [ha.ne', hb.ne', hc.ne', hn.ne',
    hg1, hg2, hg3, hg4]


end TupleModel

private def finToTuple : Point3 ≃ᵐ TupleModel.Point3 :=
  (MeasurableEquiv.piFinSuccAbove
      (fun _i : Fin 3 => ℝ) (0 : Fin 3)).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.piFinTwo (fun _i : Fin 2 => ℝ)))

@[simp] private theorem finToTuple_apply (p : Point3) :
    finToTuple p = (p 0, p 1, p 2) := by
  rfl

private theorem finToTuple_measurePreserving :
    MeasurePreserving finToTuple volume volume := by
  have h₁ :
      MeasurePreserving
        (MeasurableEquiv.piFinSuccAbove
          (fun _i : Fin 3 => ℝ) (0 : Fin 3)) volume volume :=
    volume_preserving_piFinSuccAbove (fun _i : Fin 3 => ℝ) (0 : Fin 3)
  have h₂ :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl ℝ)
          (MeasurableEquiv.piFinTwo (fun _i : Fin 2 => ℝ)))
        volume volume := by
    exact (MeasurePreserving.id (volume : Measure ℝ)).prod
      (volume_preserving_piFinTwo (fun _i : Fin 2 => ℝ))
  exact h₂.comp h₁

private theorem finToTuple_preimage_solid
    (a b c n : ℝ) :
    finToTuple ⁻¹' TupleModel.solid a b c n =
      superellipsoid a b c n := by
  ext p
  simp only [Set.mem_preimage, TupleModel.solid, superellipsoid,
    Set.mem_setOf_eq, finToTuple_apply]

private theorem setIntegral_finToTuple
    (S : Set TupleModel.Point3) (hS : MeasurableSet S)
    (f : TupleModel.Point3 → ℝ) :
    (∫ p in finToTuple ⁻¹' S, f (finToTuple p)) =
      ∫ q in S, f q := by
  have h :=
    finToTuple_measurePreserving.integral_comp' (S.indicator f)
  rw [← MeasureTheory.integral_indicator
      (hS.preimage finToTuple.measurable),
    ← MeasureTheory.integral_indicator hS]
  simpa only [Function.comp_apply] using h

private theorem mass_eq_tupleMass
    (a b c n : ℝ) (hn : 0 < n) :
    mass a b c n = TupleModel.mass a b c n := by
  have hs : MeasurableSet (TupleModel.solid a b c n) :=
    (TupleModel.solid_closed a b c n hn).measurableSet
  unfold mass TupleModel.mass
  rw [← finToTuple_preimage_solid]
  simpa using
    (setIntegral_finToTuple
      (TupleModel.solid a b c n) hs
      (fun _q : TupleModel.Point3 => (1 : ℝ)))

private theorem xMoment_eq_tuple
    (a b c n : ℝ) (hn : 0 < n) :
    (∫ p in superellipsoid a b c n, p 0) =
      ∫ q in TupleModel.solid a b c n, q.1 := by
  have hs : MeasurableSet (TupleModel.solid a b c n) :=
    (TupleModel.solid_closed a b c n hn).measurableSet
  rw [← finToTuple_preimage_solid]
  simpa using
    (setIntegral_finToTuple
      (TupleModel.solid a b c n) hs
      (fun q : TupleModel.Point3 => q.1))

private theorem yMoment_eq_tuple
    (a b c n : ℝ) (hn : 0 < n) :
    (∫ p in superellipsoid a b c n, p 1) =
      ∫ q in TupleModel.solid a b c n, q.2.1 := by
  have hs : MeasurableSet (TupleModel.solid a b c n) :=
    (TupleModel.solid_closed a b c n hn).measurableSet
  rw [← finToTuple_preimage_solid]
  simpa using
    (setIntegral_finToTuple
      (TupleModel.solid a b c n) hs
      (fun q : TupleModel.Point3 => q.2.1))

private theorem zMoment_eq_tuple
    (a b c n : ℝ) (hn : 0 < n) :
    (∫ p in superellipsoid a b c n, p 2) =
      ∫ q in TupleModel.solid a b c n, q.2.2 := by
  have hs : MeasurableSet (TupleModel.solid a b c n) :=
    (TupleModel.solid_closed a b c n hn).measurableSet
  rw [← finToTuple_preimage_solid]
  simpa using
    (setIntegral_finToTuple
      (TupleModel.solid a b c n) hs
      (fun q : TupleModel.Point3 => q.2.2))

private theorem mass_formula
    (a b c n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : 0 < n) :
    mass a b c n =
      a * b * c / (3 * n ^ 2) *
        (Real.Gamma (1 / n) ^ 3 / Real.Gamma (3 / n)) := by
  rw [mass_eq_tupleMass a b c n hn]
  exact TupleModel.mass_formula a b c n ha hb hc hn

private theorem xMoment_formula
    (a b c n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : 0 < n) :
    (∫ p in superellipsoid a b c n, p 0) =
      a ^ 2 * b * c / (4 * n ^ 2) *
        (Real.Gamma (1 / n) ^ 2 * Real.Gamma (2 / n) /
          Real.Gamma (4 / n)) := by
  rw [xMoment_eq_tuple a b c n hn]
  exact TupleModel.xMoment_formula a b c n ha hb hc hn

private theorem yMoment_formula
    (a b c n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : 0 < n) :
    (∫ p in superellipsoid a b c n, p 1) =
      a * b ^ 2 * c / (4 * n ^ 2) *
        (Real.Gamma (1 / n) ^ 2 * Real.Gamma (2 / n) /
          Real.Gamma (4 / n)) := by
  rw [yMoment_eq_tuple a b c n hn]
  exact TupleModel.yMoment_formula a b c n ha hb hc hn

private theorem zMoment_formula
    (a b c n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : 0 < n) :
    (∫ p in superellipsoid a b c n, p 2) =
      a * b * c ^ 2 / (4 * n ^ 2) *
        (Real.Gamma (1 / n) ^ 2 * Real.Gamma (2 / n) /
          Real.Gamma (4 / n)) := by
  rw [zMoment_eq_tuple a b c n hn]
  exact TupleModel.zMoment_formula a b c n ha hb hc hn

private theorem square_rpow_mul
    (x u : ℝ) (hx : 0 < x) :
    Real.rpow (x ^ 2) (u - 1) * x =
      Real.rpow x (2 * u - 1) := by
  calc
    Real.rpow (x ^ 2) (u - 1) * x =
        Real.rpow x (2 * (u - 1)) * x := by
      exact congrArg (fun t : ℝ => t * x)
        (Real.rpow_natCast_mul hx.le 2 (u - 1)).symm
    _ = Real.rpow x (2 * (u - 1) + 1) :=
      (Real.rpow_add_one hx.ne' (2 * (u - 1))).symm
    _ = Real.rpow x (2 * u - 1) := by
      congr 1
      ring

private theorem trig_rpow_integral
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    (∫ θ in (0 : ℝ)..Real.pi / 2,
        Real.rpow (Real.sin θ) (2 * u - 1) *
          Real.rpow (Real.cos θ) (2 * v - 1)) =
      1 / 2 * TupleModel.betaFn v u := by
  let f : ℝ → ℝ := fun θ => Real.sin θ ^ 2
  let f' : ℝ → ℝ := fun θ => 2 * Real.sin θ * Real.cos θ
  let g : ℝ → ℝ := fun t =>
    Real.rpow (1 - t) (v - 1) * Real.rpow t (u - 1)
  have hhalf : 0 ≤ Real.pi / 2 := by positivity
  have hfderiv :
      ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        HasDerivWithinAt f (f' θ)
          (Set.Icc (0 : ℝ) (Real.pi / 2)) θ := by
    intro θ hθ
    dsimp [f, f']
    convert ((Real.hasDerivAt_sin θ).pow 2).hasDerivWithinAt
      using 1 <;> ring <;> rfl
  have hfmono :
      MonotoneOn f (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    intro x hx y hy hxy
    have hx' : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨(neg_nonpos.mpr hhalf).trans hx.1, hx.2⟩
    have hy' : y ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨(neg_nonpos.mpr hhalf).trans hy.1, hy.2⟩
    have hsle : Real.sin x ≤ Real.sin y :=
      Real.monotoneOn_sin hx' hy' hxy
    have hsx : 0 ≤ Real.sin x :=
      Real.sin_nonneg_of_nonneg_of_le_pi hx.1
        (hx.2.trans (by linarith [Real.pi_pos]))
    have hsy : 0 ≤ Real.sin y :=
      Real.sin_nonneg_of_nonneg_of_le_pi hy.1
        (hy.2.trans (by linarith [Real.pi_pos]))
    dsimp [f]
    nlinarith
  have hfcont :
      ContinuousOn f (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    fun_prop
  have hfimage :
      f '' Set.Icc (0 : ℝ) (Real.pi / 2) =
        Set.Icc (0 : ℝ) 1 := by
    have h :=
      hfcont.image_Icc_of_monotoneOn hhalf hfmono
    simpa [f, Real.sin_pi_div_two] using h
  have hchange :=
    MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
      (f := f) (f' := f') (g := g)
      (s := Set.Icc (0 : ℝ) (Real.pi / 2))
      measurableSet_Icc hfderiv hfmono
  rw [hfimage] at hchange
  have hbeta :
      TupleModel.betaFn v u =
        ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          f' θ * g (f θ) := by
    unfold TupleModel.betaFn
    rw [intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc]
    rw [hchange, integral_Icc_eq_integral_Ioo]
    rfl
  have hpoint :
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        f' θ * g (f θ) =
          2 *
            (Real.rpow (Real.sin θ) (2 * u - 1) *
              Real.rpow (Real.cos θ) (2 * v - 1)) := by
    intro θ hθ
    have hs : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1
        (hθ.2.trans (by linarith [Real.pi_pos]))
    have hc : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo
        ⟨(neg_lt_zero.mpr (by positivity : 0 < Real.pi / 2)).trans hθ.1,
          hθ.2⟩
    have htrig :
        1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    dsimp [f, f', g]
    rw [htrig]
    calc
      2 * Real.sin θ * Real.cos θ *
            (Real.rpow (Real.cos θ ^ 2) (v - 1) *
              Real.rpow (Real.sin θ ^ 2) (u - 1)) =
          2 *
            ((Real.rpow (Real.sin θ ^ 2) (u - 1) *
                Real.sin θ) *
              (Real.rpow (Real.cos θ ^ 2) (v - 1) *
                Real.cos θ)) := by ring
      _ = 2 *
            (Real.rpow (Real.sin θ) (2 * u - 1) *
              Real.rpow (Real.cos θ) (2 * v - 1)) := by
        rw [square_rpow_mul (Real.sin θ) u hs,
          square_rpow_mul (Real.cos θ) v hc]
  rw [hbeta]
  have hset :
      (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          f' θ * g (f θ)) =
        ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          2 *
            (Real.rpow (Real.sin θ) (2 * u - 1) *
              Real.rpow (Real.cos θ) (2 * v - 1)) := by
    exact setIntegral_congr_fun measurableSet_Ioo hpoint
  rw [hset, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hhalf,
    intervalIntegral.integral_const_mul]
  ring

private def phiWeight (n φ : ℝ) : ℝ :=
  Real.rpow (Real.sin φ) (2 / n - 1) *
    Real.rpow (Real.cos φ) (2 / n - 1)

private def psiWeight (n ψ : ℝ) : ℝ :=
  Real.rpow (Real.sin ψ) (2 / n - 1) *
    Real.rpow (Real.cos ψ) (4 / n - 1)

private theorem phiWeight_integral
    (n : ℝ) (hn : 0 < n) :
    (∫ φ in (0 : ℝ)..Real.pi / 2, phiWeight n φ) =
      1 / 2 * TupleModel.betaFn (1 / n) (1 / n) := by
  unfold phiWeight
  convert trig_rpow_integral (1 / n) (1 / n)
      (one_div_pos.mpr hn) (one_div_pos.mpr hn) using 1 <;>
    field_simp [hn.ne'] <;> ring

private theorem psiWeight_integral
    (n : ℝ) (hn : 0 < n) :
    (∫ ψ in (0 : ℝ)..Real.pi / 2, psiWeight n ψ) =
      1 / 2 * TupleModel.betaFn (2 / n) (1 / n) := by
  unfold psiWeight
  convert trig_rpow_integral (1 / n) (2 / n)
      (one_div_pos.mpr hn) (div_pos (by norm_num) hn) using 1 <;>
    field_simp [hn.ne'] <;> ring

private theorem radial_weight_integral
    (n φ ψ : ℝ) :
    (∫ r in (0 : ℝ)..1,
        r ^ 2 * phiWeight n φ * psiWeight n ψ) =
      1 / 3 * phiWeight n φ * psiWeight n ψ := by
  calc
    (∫ r in (0 : ℝ)..1,
        r ^ 2 * phiWeight n φ * psiWeight n ψ) =
        ∫ r in (0 : ℝ)..1,
          (phiWeight n φ * psiWeight n ψ) * r ^ 2 := by
      apply intervalIntegral.integral_congr
      intro r hr
      ring
    _ = (phiWeight n φ * psiWeight n ψ) *
        ∫ r in (0 : ℝ)..1, r ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
    _ = 1 / 3 * phiWeight n φ * psiWeight n ψ := by
      rw [integral_pow]
      norm_num
      ring

private theorem parameter_integral_value
    (n : ℝ) (hn : 0 < n) :
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        ∫ ψ in (0 : ℝ)..Real.pi / 2,
          ∫ r in (0 : ℝ)..1,
            r ^ 2 * phiWeight n φ * psiWeight n ψ) =
      1 / 12 *
        (TupleModel.betaFn (1 / n) (1 / n) *
          TupleModel.betaFn (2 / n) (1 / n)) := by
  simp_rw [radial_weight_integral]
  have hinner (φ : ℝ) :
      (∫ ψ in (0 : ℝ)..Real.pi / 2,
          1 / 3 * phiWeight n φ * psiWeight n ψ) =
        (1 / 3 * phiWeight n φ) *
          (1 / 2 * TupleModel.betaFn (2 / n) (1 / n)) := by
    rw [intervalIntegral.integral_const_mul,
      psiWeight_integral n hn]
  simp_rw [hinner]
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const_mul,
    phiWeight_integral n hn]
  ring

private theorem beta_parameter_product_value
    (n : ℝ) (hn : 0 < n) :
    TupleModel.betaFn (1 / n) (1 / n) *
        TupleModel.betaFn (2 / n) (1 / n) =
      Real.Gamma (1 / n) ^ 3 / Real.Gamma (3 / n) := by
  have h1 : 0 < 1 / n := one_div_pos.mpr hn
  have h2 : 0 < 2 / n := div_pos (by norm_num) hn
  have h3 : 0 < 3 / n := div_pos (by norm_num) hn
  rw [TupleModel.betaFn_eq_Gamma_mul_div
      (1 / n) (1 / n) h1 h1,
    TupleModel.betaFn_eq_Gamma_mul_div
      (2 / n) (1 / n) h2 h1]
  have hs2 : 1 / n + 1 / n = 2 / n := by
    field_simp [hn.ne']
    ring
  have hs3 : 2 / n + 1 / n = 3 / n := by
    field_simp [hn.ne']
    ring
  rw [hs2, hs3]
  have hg2 : Real.Gamma (2 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos h2).ne'
  have hg3 : Real.Gamma (3 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos h3).ne'
  field_simp [hg2, hg3]

private theorem hasDerivAt_cos_rpow
    (k t : ℝ) (hcos : Real.cos t ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.rpow (Real.cos x) k)
      (-k * Real.sin t * Real.rpow (Real.cos t) (k - 1)) t := by
  have h :=
    (Real.hasDerivAt_rpow_const (p := k) (Or.inl hcos)).comp
      t (Real.hasDerivAt_cos t)
  change
    HasDerivAt (fun x : ℝ => Real.rpow (Real.cos x) k)
      ((k * Real.rpow (Real.cos t) (k - 1)) * (-Real.sin t)) t
    at h
  convert h using 1 <;> ring

private theorem hasDerivAt_sin_rpow
    (k t : ℝ) (hsin : Real.sin t ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.rpow (Real.sin x) k)
      (k * Real.cos t * Real.rpow (Real.sin t) (k - 1)) t := by
  have h :=
    (Real.hasDerivAt_rpow_const (p := k) (Or.inl hsin)).comp
      t (Real.hasDerivAt_sin t)
  change
    HasDerivAt (fun x : ℝ => Real.rpow (Real.sin x) k)
      ((k * Real.rpow (Real.sin t) (k - 1)) * Real.cos t) t
    at h
  convert h using 1 <;> ring

private theorem coordinateJacobian_parameterization
    (a b c n r φ ψ : ℝ)
    (hcosφ : Real.cos φ ≠ 0) (hsinφ : Real.sin φ ≠ 0)
    (hcosψ : Real.cos ψ ≠ 0) (hsinψ : Real.sin ψ ≠ 0) :
    coordinateJacobian (parameterization a b c n) ![r, φ, ψ] =
      ![
        ![
          a * Real.rpow (Real.cos φ) (2 / n) *
            Real.rpow (Real.cos ψ) (2 / n),
          -(a * r * (2 / n) * Real.sin φ *
            Real.rpow (Real.cos φ) (2 / n - 1) *
            Real.rpow (Real.cos ψ) (2 / n)),
          -(a * r * (2 / n) *
            Real.rpow (Real.cos φ) (2 / n) * Real.sin ψ *
            Real.rpow (Real.cos ψ) (2 / n - 1))],
        ![
          b * Real.rpow (Real.sin φ) (2 / n) *
            Real.rpow (Real.cos ψ) (2 / n),
          b * r * (2 / n) * Real.cos φ *
            Real.rpow (Real.sin φ) (2 / n - 1) *
            Real.rpow (Real.cos ψ) (2 / n),
          -(b * r * (2 / n) *
            Real.rpow (Real.sin φ) (2 / n) * Real.sin ψ *
            Real.rpow (Real.cos ψ) (2 / n - 1))],
        ![
          c * Real.rpow (Real.sin ψ) (2 / n),
          0,
          c * r * (2 / n) * Real.cos ψ *
            Real.rpow (Real.sin ψ) (2 / n - 1)] ] := by
  ext i j
  fin_cases i <;> fin_cases j
  · change
      deriv (fun t : ℝ =>
        a * t *
          Real.rpow (Real.cos φ) (2 / n) *
          Real.rpow (Real.cos ψ) (2 / n)) r =
        a * Real.rpow (Real.cos φ) (2 / n) *
          Real.rpow (Real.cos ψ) (2 / n)
    apply HasDerivAt.deriv
    convert
      (((hasDerivAt_id r).const_mul a).mul_const
        (Real.rpow (Real.cos φ) (2 / n))).mul_const
          (Real.rpow (Real.cos ψ) (2 / n))
      using 1 <;> ring <;> rfl
  · change
      deriv (fun t : ℝ =>
        a * r * Real.rpow (Real.cos t) (2 / n) *
          Real.rpow (Real.cos ψ) (2 / n)) φ =
        -(a * r * (2 / n) * Real.sin φ *
          Real.rpow (Real.cos φ) (2 / n - 1) *
          Real.rpow (Real.cos ψ) (2 / n))
    apply HasDerivAt.deriv
    convert
      ((hasDerivAt_cos_rpow (2 / n) φ hcosφ).const_mul
        (a * r)).mul_const (Real.rpow (Real.cos ψ) (2 / n))
      using 1 <;> ring <;> rfl
  · change
      deriv (fun t : ℝ =>
        a * r * Real.rpow (Real.cos φ) (2 / n) *
          Real.rpow (Real.cos t) (2 / n)) ψ =
        -(a * r * (2 / n) *
          Real.rpow (Real.cos φ) (2 / n) * Real.sin ψ *
          Real.rpow (Real.cos ψ) (2 / n - 1))
    apply HasDerivAt.deriv
    convert
      (hasDerivAt_cos_rpow (2 / n) ψ hcosψ).const_mul
        (a * r * Real.rpow (Real.cos φ) (2 / n))
      using 1 <;> ring <;> rfl
  · change
      deriv (fun t : ℝ =>
        b * t * Real.rpow (Real.sin φ) (2 / n) *
          Real.rpow (Real.cos ψ) (2 / n)) r =
        b * Real.rpow (Real.sin φ) (2 / n) *
          Real.rpow (Real.cos ψ) (2 / n)
    apply HasDerivAt.deriv
    convert
      (((hasDerivAt_id r).const_mul b).mul_const
        (Real.rpow (Real.sin φ) (2 / n))).mul_const
          (Real.rpow (Real.cos ψ) (2 / n))
      using 1 <;> ring <;> rfl
  · change
      deriv (fun t : ℝ =>
        b * r * Real.rpow (Real.sin t) (2 / n) *
          Real.rpow (Real.cos ψ) (2 / n)) φ =
        b * r * (2 / n) * Real.cos φ *
          Real.rpow (Real.sin φ) (2 / n - 1) *
          Real.rpow (Real.cos ψ) (2 / n)
    apply HasDerivAt.deriv
    convert
      ((hasDerivAt_sin_rpow (2 / n) φ hsinφ).const_mul
        (b * r)).mul_const (Real.rpow (Real.cos ψ) (2 / n))
      using 1 <;> ring <;> rfl
  · change
      deriv (fun t : ℝ =>
        b * r * Real.rpow (Real.sin φ) (2 / n) *
          Real.rpow (Real.cos t) (2 / n)) ψ =
        -(b * r * (2 / n) *
          Real.rpow (Real.sin φ) (2 / n) * Real.sin ψ *
          Real.rpow (Real.cos ψ) (2 / n - 1))
    apply HasDerivAt.deriv
    convert
      (hasDerivAt_cos_rpow (2 / n) ψ hcosψ).const_mul
        (b * r * Real.rpow (Real.sin φ) (2 / n))
      using 1 <;> ring
  · change
      deriv (fun t : ℝ =>
        c * t * Real.rpow (Real.sin ψ) (2 / n)) r =
        c * Real.rpow (Real.sin ψ) (2 / n)
    apply HasDerivAt.deriv
    convert ((hasDerivAt_id r).const_mul c).mul_const
      (Real.rpow (Real.sin ψ) (2 / n)) using 1 <;> ring <;> rfl
  · change
      deriv (fun _t : ℝ =>
        c * r * Real.rpow (Real.sin ψ) (2 / n)) φ = 0
    exact (hasDerivAt_const φ
      (c * r * Real.rpow (Real.sin ψ) (2 / n))).deriv
  · change
      deriv (fun t : ℝ =>
        c * r * Real.rpow (Real.sin t) (2 / n)) ψ =
        c * r * (2 / n) * Real.cos ψ *
          Real.rpow (Real.sin ψ) (2 / n - 1)
    apply HasDerivAt.deriv
    convert
      (hasDerivAt_sin_rpow (2 / n) ψ hsinψ).const_mul (c * r)
      using 1 <;> ring <;> rfl

private theorem rpow_eq_mul_rpow_sub_one
    (x k : ℝ) (hx : 0 < x) :
    Real.rpow x k = x * Real.rpow x (k - 1) := by
  have h := Real.rpow_add_one hx.ne' (k - 1)
  change
    Real.rpow x ((k - 1) + 1) =
      Real.rpow x (k - 1) * x at h
  calc
    Real.rpow x k = Real.rpow x ((k - 1) + 1) := by
      congr 1
      ring
    _ = Real.rpow x (k - 1) * x := h
    _ = x * Real.rpow x (k - 1) := by ring

private theorem rpow_two_mul_sub_one
    (x k : ℝ) (hx : 0 < x) :
    Real.rpow x (2 * k - 1) =
      x * Real.rpow x (k - 1) ^ 2 := by
  have hadd := Real.rpow_add hx (k - 1) (k - 1)
  change
    Real.rpow x ((k - 1) + (k - 1)) =
      Real.rpow x (k - 1) * Real.rpow x (k - 1) at hadd
  have hone := Real.rpow_add_one hx.ne' ((k - 1) + (k - 1))
  change
    Real.rpow x (((k - 1) + (k - 1)) + 1) =
      Real.rpow x ((k - 1) + (k - 1)) * x at hone
  calc
    Real.rpow x (2 * k - 1) =
        Real.rpow x (((k - 1) + (k - 1)) + 1) := by
      congr 1
      ring
    _ = Real.rpow x ((k - 1) + (k - 1)) * x := hone
    _ = (Real.rpow x (k - 1) * Real.rpow x (k - 1)) * x := by
      rw [hadd]
    _ = x * Real.rpow x (k - 1) ^ 2 := by ring

theorem gap1 (a b c n r φ ψ : ℝ)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : 0 < r)
    (hφ₀ : 0 < φ) (hφ₁ : φ < Real.pi / 2)
    (hψ₀ : 0 < ψ) (hψ₁ : ψ < Real.pi / 2) :
    jacobianAbs (parameterization a b c n) ![r, φ, ψ] =
      jacobianDensity a b c n r φ ψ := by
  have hsinφ : 0 < Real.sin φ :=
    Real.sin_pos_of_pos_of_lt_pi hφ₀
      (hφ₁.trans (by linarith [Real.pi_pos]))
  have hcosφ : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo
      ⟨(neg_lt_zero.mpr (by positivity : 0 < Real.pi / 2)).trans hφ₀,
        hφ₁⟩
  have hsinψ : 0 < Real.sin ψ :=
    Real.sin_pos_of_pos_of_lt_pi hψ₀
      (hψ₁.trans (by linarith [Real.pi_pos]))
  have hcosψ : 0 < Real.cos ψ :=
    Real.cos_pos_of_mem_Ioo
      ⟨(neg_lt_zero.mpr (by positivity : 0 < Real.pi / 2)).trans hψ₀,
        hψ₁⟩
  have hCφ :=
    rpow_eq_mul_rpow_sub_one
      (Real.cos φ) (2 / n) hcosφ
  have hSφ :=
    rpow_eq_mul_rpow_sub_one
      (Real.sin φ) (2 / n) hsinφ
  have hCψ :=
    rpow_eq_mul_rpow_sub_one
      (Real.cos ψ) (2 / n) hcosψ
  have hSψ :=
    rpow_eq_mul_rpow_sub_one
      (Real.sin ψ) (2 / n) hsinψ
  have hCφ' :
      Real.cos φ ^ (2 / n) =
        Real.cos φ * Real.rpow (Real.cos φ) (2 / n - 1) :=
    hCφ
  have hSφ' :
      Real.sin φ ^ (2 / n) =
        Real.sin φ * Real.rpow (Real.sin φ) (2 / n - 1) :=
    hSφ
  have hCψ' :
      Real.cos ψ ^ (2 / n) =
        Real.cos ψ * Real.rpow (Real.cos ψ) (2 / n - 1) :=
    hCψ
  have hSψ' :
      Real.sin ψ ^ (2 / n) =
        Real.sin ψ * Real.rpow (Real.sin ψ) (2 / n - 1) :=
    hSψ
  have hCφm :
      Real.cos φ ^ (2 / n - 1) =
        Real.rpow (Real.cos φ) (2 / n - 1) := by
    rfl
  have hSφm :
      Real.sin φ ^ (2 / n - 1) =
        Real.rpow (Real.sin φ) (2 / n - 1) := by
    rfl
  have hCψm :
      Real.cos ψ ^ (2 / n - 1) =
        Real.rpow (Real.cos ψ) (2 / n - 1) := by
    rfl
  have hSψm :
      Real.sin ψ ^ (2 / n - 1) =
        Real.rpow (Real.sin ψ) (2 / n - 1) := by
    rfl
  have hCψ₂ :
      Real.rpow (Real.cos ψ) (4 / n - 1) =
        Real.cos ψ *
          Real.rpow (Real.cos ψ) (2 / n - 1) ^ 2 := by
    convert
      rpow_two_mul_sub_one
        (Real.cos ψ) (2 / n) hcosψ
      using 1 <;> field_simp [hn.ne'] <;> ring
  have htrigφ :
      Real.sin φ ^ 2 = 1 - Real.cos φ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq φ]
  have htrigψ :
      Real.sin ψ ^ 2 = 1 - Real.cos ψ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq ψ]
  have hdet :
      Matrix.det
          (coordinateJacobian
            (parameterization a b c n) ![r, φ, ψ]) =
        jacobianDensity a b c n r φ ψ := by
    rw [coordinateJacobian_parameterization
      a b c n r φ ψ hcosφ.ne' hsinφ.ne' hcosψ.ne' hsinψ.ne',
      Matrix.det_fin_three]
    simp
    unfold jacobianDensity
    rw [hCφm, hSφm, hCψm, hSψm,
      hCφ', hSφ', hCψ', hSψ', hCψ₂]
    ring_nf
    rw [htrigφ, htrigψ]
    ring
  unfold jacobianAbs
  rw [hdet, abs_of_pos]
  unfold jacobianDensity
  have hn2 : 0 < n ^ 2 := sq_pos_of_pos hn
  have hpSφ :
      0 < Real.rpow (Real.sin φ) (2 / n - 1) :=
    Real.rpow_pos_of_pos hsinφ _
  have hpCφ :
      0 < Real.rpow (Real.cos φ) (2 / n - 1) :=
    Real.rpow_pos_of_pos hcosφ _
  have hpCψ :
      0 < Real.rpow (Real.cos ψ) (4 / n - 1) :=
    Real.rpow_pos_of_pos hcosψ _
  have hpSψ :
      0 < Real.rpow (Real.sin ψ) (2 / n - 1) :=
    Real.rpow_pos_of_pos hsinψ _
  positivity

theorem gap3 (a b c n : ℝ)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    4 / n ^ 2 * a * b * c *
        (∫ φ in (0 : ℝ)..Real.pi / 2,
          ∫ ψ in (0 : ℝ)..Real.pi / 2,
            ∫ r in (0 : ℝ)..1,
              r ^ 2 *
                Real.rpow (Real.sin φ) (2 / n - 1) *
                Real.rpow (Real.cos φ) (2 / n - 1) *
                Real.rpow (Real.cos ψ) (4 / n - 1) *
                Real.rpow (Real.sin ψ) (2 / n - 1)) =
      a * b * c / (3 * n ^ 2) *
        (Real.Gamma (1 / n) ^ 3 / Real.Gamma (3 / n)) := by
  have hshape :
      (∫ φ in (0 : ℝ)..Real.pi / 2,
          ∫ ψ in (0 : ℝ)..Real.pi / 2,
            ∫ r in (0 : ℝ)..1,
              r ^ 2 *
                Real.rpow (Real.sin φ) (2 / n - 1) *
                Real.rpow (Real.cos φ) (2 / n - 1) *
                Real.rpow (Real.cos ψ) (4 / n - 1) *
                Real.rpow (Real.sin ψ) (2 / n - 1)) =
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          ∫ ψ in (0 : ℝ)..Real.pi / 2,
            ∫ r in (0 : ℝ)..1,
              r ^ 2 * phiWeight n φ * psiWeight n ψ := by
    apply intervalIntegral.integral_congr
    intro φ hφ
    apply intervalIntegral.integral_congr
    intro ψ hψ
    apply intervalIntegral.integral_congr
    intro r hr
    unfold phiWeight psiWeight
    ring
  rw [hshape, parameter_integral_value n hn,
    beta_parameter_product_value n hn]
  ring

theorem gap4 (a b c n : ℝ)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    mass a b c n =
      a * b * c / (3 * n ^ 2) *
        (Real.Gamma (1 / n) ^ 3 / Real.Gamma (3 / n)) := by
  exact mass_formula a b c n ha hb hc hn

theorem gap2 (a b c n : ℝ)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    mass a b c n =
      4 / n ^ 2 * a * b * c *
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          ∫ ψ in (0 : ℝ)..Real.pi / 2,
            ∫ r in (0 : ℝ)..1,
              r ^ 2 *
                Real.rpow (Real.sin φ) (2 / n - 1) *
                Real.rpow (Real.cos φ) (2 / n - 1) *
                Real.rpow (Real.cos ψ) (4 / n - 1) *
                Real.rpow (Real.sin ψ) (2 / n - 1) := by
  exact (gap4 a b c n hn ha hb hc).trans
    (gap3 a b c n hn ha hb hc).symm

theorem gap5 (a b c n : ℝ)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    xCentroid a b c n =
      1 / mass a b c n *
        (a ^ 2 * b * c / (4 * n ^ 2)) *
          (Real.Gamma (1 / n) ^ 2 * Real.Gamma (2 / n) /
            Real.Gamma (4 / n)) := by
  unfold xCentroid
  rw [xMoment_formula a b c n ha hb hc hn]
  ring

theorem gap6 (a b c n : ℝ)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / mass a b c n *
        (a ^ 2 * b * c / (4 * n ^ 2)) *
          (Real.Gamma (1 / n) ^ 2 * Real.Gamma (2 / n) /
            Real.Gamma (4 / n)) =
      (3 : ℝ) / 4 *
        (Real.Gamma (2 / n) * Real.Gamma (3 / n) /
          (Real.Gamma (1 / n) * Real.Gamma (4 / n))) * a := by
  rw [mass_formula a b c n ha hb hc hn]
  have h1 : 0 < 1 / n := one_div_pos.mpr hn
  have h2 : 0 < 2 / n := div_pos (by norm_num) hn
  have h3 : 0 < 3 / n := div_pos (by norm_num) hn
  have h4 : 0 < 4 / n := div_pos (by norm_num) hn
  have hg1 : Real.Gamma (1 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos h1).ne'
  have hg2 : Real.Gamma (2 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos h2).ne'
  have hg3 : Real.Gamma (3 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos h3).ne'
  have hg4 : Real.Gamma (4 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos h4).ne'
  field_simp [ha.ne', hb.ne', hc.ne', hn.ne',
    hg1, hg2, hg3, hg4]

theorem gap7 (a b c n : ℝ)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    xCentroid a b c n =
      (3 : ℝ) / 4 *
        (Real.Gamma (2 / n) * Real.Gamma (3 / n) /
          (Real.Gamma (1 / n) * Real.Gamma (4 / n))) * a := by
  exact (gap5 a b c n hn ha hb hc).trans
    (gap6 a b c n hn ha hb hc)

theorem gap8 (a b c n : ℝ)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    yCentroid a b c n =
      (3 : ℝ) / 4 *
        (Real.Gamma (2 / n) * Real.Gamma (3 / n) /
          (Real.Gamma (1 / n) * Real.Gamma (4 / n))) * b := by
  unfold yCentroid
  rw [yMoment_formula a b c n ha hb hc hn,
    mass_formula a b c n ha hb hc hn]
  have h1 : 0 < 1 / n := one_div_pos.mpr hn
  have h2 : 0 < 2 / n := div_pos (by norm_num) hn
  have h3 : 0 < 3 / n := div_pos (by norm_num) hn
  have h4 : 0 < 4 / n := div_pos (by norm_num) hn
  have hg1 : Real.Gamma (1 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos h1).ne'
  have hg2 : Real.Gamma (2 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos h2).ne'
  have hg3 : Real.Gamma (3 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos h3).ne'
  have hg4 : Real.Gamma (4 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos h4).ne'
  field_simp [ha.ne', hb.ne', hc.ne', hn.ne',
    hg1, hg2, hg3, hg4]

theorem gap9 (a b c n : ℝ)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    zCentroid a b c n =
      (3 : ℝ) / 4 *
        (Real.Gamma (2 / n) * Real.Gamma (3 / n) /
          (Real.Gamma (1 / n) * Real.Gamma (4 / n))) * c := by
  unfold zCentroid
  rw [zMoment_formula a b c n ha hb hc hn,
    mass_formula a b c n ha hb hc hn]
  have h1 : 0 < 1 / n := one_div_pos.mpr hn
  have h2 : 0 < 2 / n := div_pos (by norm_num) hn
  have h3 : 0 < 3 / n := div_pos (by norm_num) hn
  have h4 : 0 < 4 / n := div_pos (by norm_num) hn
  have hg1 : Real.Gamma (1 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos h1).ne'
  have hg2 : Real.Gamma (2 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos h2).ne'
  have hg3 : Real.Gamma (3 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos h3).ne'
  have hg4 : Real.Gamma (4 / n) ≠ 0 :=
    (Real.Gamma_pos_of_pos h4).ne'
  field_simp [ha.ne', hb.ne', hc.ne', hn.ne',
    hg1, hg2, hg3, hg4]

theorem gap10 (a b c n : ℝ)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (xCentroid a b c n, yCentroid a b c n, zCentroid a b c n) =
      ((3 : ℝ) / 4 *
          (Real.Gamma (2 / n) * Real.Gamma (3 / n) /
            (Real.Gamma (1 / n) * Real.Gamma (4 / n))) * a,
        (3 : ℝ) / 4 *
          (Real.Gamma (2 / n) * Real.Gamma (3 / n) /
            (Real.Gamma (1 / n) * Real.Gamma (4 / n))) * b,
        (3 : ℝ) / 4 *
          (Real.Gamma (2 / n) * Real.Gamma (3 / n) /
            (Real.Gamma (1 / n) * Real.Gamma (4 / n))) * c) := by
  rw [gap7 a b c n hn ha hb hc,
    gap8 a b c n hn ha hb hc,
    gap9 a b c n hn ha hb hc]

end

end ProofGap.Exercise4141
