import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Ring.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace ProofGap.Exercise3134

noncomputable section

open Filter
open scoped BigOperators Interval Topology

def UniformConvergesOn (u : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x ∈ s, |u n x - f x| < ε

def cosineCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ u in -Real.pi..Real.pi, f u * Real.cos ((n : ℝ) * u)

def sineCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ u in -Real.pi..Real.pi, f u * Real.sin ((n : ℝ) * u)

def partialSum (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  cosineCoefficient f 0 / 2 +
    ∑ m ∈ Finset.Icc 1 n,
      (cosineCoefficient f m * Real.cos ((m : ℝ) * x) +
        sineCoefficient f m * Real.sin ((m : ℝ) * x))

def fejerMean (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  if n = 0 then partialSum f 0 x
  else 1 / (n : ℝ) * ∑ k ∈ Finset.range n, partialSum f k x

def dirichletHalfKernel (n : ℕ) (v : ℝ) : ℝ :=
  1 / 2 + ∑ m ∈ Finset.Icc 1 n, Real.cos ((m : ℝ) * v)

def dirichletQuotient (n : ℕ) (v : ℝ) : ℝ :=
  Real.sin ((2 * (n : ℝ) + 1) * (v / 2)) /
    (2 * Real.sin (v / 2))

def fejerKernel (n : ℕ) (t : ℝ) : ℝ :=
  (Real.sin ((n : ℝ) * t / 2) / Real.sin (t / 2)) ^ 2

def partialSumIntegral (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  1 / Real.pi *
    ∫ u in -Real.pi..Real.pi,
      f u * dirichletHalfKernel n (u - x)

def symmetricPartialIntegral (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  1 / Real.pi *
    ∫ t in (0 : ℝ)..Real.pi,
      (f (x + t) + f (x - t)) *
        (Real.sin (((n : ℝ) + 1 / 2) * t) /
          (2 * Real.sin (t / 2)))

def fejerIntegral (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  1 / (2 * (n : ℝ) * Real.pi) *
    ∫ t in (0 : ℝ)..Real.pi,
      (f (x + t) + f (x - t)) * fejerKernel n t

def errorDifference (f : ℝ → ℝ) (x t : ℝ) : ℝ :=
  f (x + t) - f x + f (x - t) - f x

def errorIntegral (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  1 / (2 * (n : ℝ) * Real.pi) *
    ∫ t in (0 : ℝ)..Real.pi,
      errorDifference f x t * fejerKernel n t

def nearError (f : ℝ → ℝ) (n : ℕ) (x τ : ℝ) : ℝ :=
  1 / (2 * (n : ℝ) * Real.pi) *
    ∫ t in (0 : ℝ)..τ,
      errorDifference f x t * fejerKernel n t

def farError (f : ℝ → ℝ) (n : ℕ) (x τ : ℝ) : ℝ :=
  1 / (2 * (n : ℝ) * Real.pi) *
    ∫ t in τ..Real.pi,
      errorDifference f x t * fejerKernel n t

def HasContinuousPeriodicExtension (f : ℝ → ℝ) : Prop :=
  ∃ F : ℝ → ℝ,
    Continuous F ∧
    Function.Periodic F (2 * Real.pi) ∧
    ∀ x ∈ Set.Icc (-Real.pi) Real.pi, F x = f x

def sawtoothLimit (x : ℝ) : ℝ :=
  if x = -Real.pi ∨ x = Real.pi then 0 else x

private theorem partialSum_continuous (f : ℝ → ℝ) (n : ℕ) :
    Continuous (partialSum f n) := by
  unfold partialSum
  fun_prop

private theorem partialSum_endpoints (f : ℝ → ℝ) (n : ℕ) :
    partialSum f n (-Real.pi) = partialSum f n Real.pi := by
  unfold partialSum
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  have hcos :
      Real.cos ((m : ℝ) * (-Real.pi)) =
        Real.cos ((m : ℝ) * Real.pi) := by
    rw [mul_neg, Real.cos_neg]
  have hsin :
      Real.sin ((m : ℝ) * (-Real.pi)) =
        Real.sin ((m : ℝ) * Real.pi) := by
    rw [mul_neg, Real.sin_neg]
    have hz : Real.sin ((m : ℝ) * Real.pi) = 0 := by
      simpa [mul_comm] using Real.sin_nat_mul_pi m
    rw [hz, neg_zero]
  rw [hcos, hsin]

private theorem fejerMean_continuous (f : ℝ → ℝ) (n : ℕ) :
    Continuous (fejerMean f n) := by
  unfold fejerMean
  split_ifs
  · exact partialSum_continuous f 0
  · exact continuous_const.mul
      (continuous_finset_sum _ fun k _ => partialSum_continuous f k)

private theorem fejerMean_endpoints (f : ℝ → ℝ) (n : ℕ) :
    fejerMean f n (-Real.pi) = fejerMean f n Real.pi := by
  unfold fejerMean
  split_ifs
  · exact partialSum_endpoints f 0
  · congr 1
    apply Finset.sum_congr rfl
    intro k hk
    exact partialSum_endpoints f k

private theorem dirichletHalfKernel_even (n : ℕ) (t : ℝ) :
    dirichletHalfKernel n (-t) = dirichletHalfKernel n t := by
  unfold dirichletHalfKernel
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [mul_neg, Real.cos_neg]

private theorem dirichletHalfKernel_periodic (n : ℕ) :
    Function.Periodic (dirichletHalfKernel n) (2 * Real.pi) := by
  intro t
  unfold dirichletHalfKernel
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [mul_add]
  have hmul :
      (m : ℝ) * (2 * Real.pi) = (m : ℕ) * (2 * Real.pi) := rfl
  rw [hmul, Real.cos_add_nat_mul_two_pi]

/--
Source: `proof_gap/exercise_3134/1.txt`; the blanket negation is false.
For the Fejér means of `f`, endpoint mismatch is the obstruction.
-/
theorem gap1 (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (-Real.pi) Real.pi))
    (hend : f (-Real.pi) ≠ f Real.pi) :
    ¬UniformConvergesOn (fejerMean f) f
      (Set.Ioo (-Real.pi) Real.pi) := by
  intro hu
  let d := dist (f (-Real.pi)) (f Real.pi)
  have hd : 0 < d := dist_pos.mpr hend
  let ε := d / 7
  have hε : 0 < ε := by positivity
  rcases hu ε hε with ⟨N, hN⟩
  let g := fejerMean f N
  have hg : Continuous g := fejerMean_continuous f N
  have hgend : g (-Real.pi) = g Real.pi := fejerMean_endpoints f N
  have hLmem : -Real.pi ∈ Set.Icc (-Real.pi) Real.pi := by
    exact ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hRmem : Real.pi ∈ Set.Icc (-Real.pi) Real.pi := by
    exact ⟨by linarith [Real.pi_pos], le_rfl⟩
  rcases (Metric.continuousOn_iff.mp hf (-Real.pi) hLmem ε hε) with
    ⟨δfL, hδfL, hfL⟩
  rcases (Metric.continuousOn_iff.mp hf Real.pi hRmem ε hε) with
    ⟨δfR, hδfR, hfR⟩
  rcases (Metric.continuousAt_iff.mp (hg.continuousAt) ε hε) with
    ⟨δgL, hδgL, hgL⟩
  rcases (Metric.continuousAt_iff.mp (hg.continuousAt) ε hε) with
    ⟨δgR, hδgR, hgR⟩
  let r := min (δfL / 2)
    (min (δfR / 2) (min (δgL / 2) (min (δgR / 2) Real.pi)))
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrfL : r < δfL :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrfR : r < δfR := by
    have := min_le_left (δfR / 2)
      (min (δgL / 2) (min (δgR / 2) Real.pi))
    exact lt_of_le_of_lt (le_trans (min_le_right _ _) this) (by linarith)
  have hrgL : r < δgL := by
    have h₁ := min_le_right (δfR / 2)
      (min (δgL / 2) (min (δgR / 2) Real.pi))
    have h₂ := min_le_left (δgL / 2) (min (δgR / 2) Real.pi)
    exact lt_of_le_of_lt (le_trans (min_le_right _ _) (le_trans h₁ h₂)) (by linarith)
  have hrgR : r < δgR := by
    have h₁ := min_le_right (δfR / 2)
      (min (δgL / 2) (min (δgR / 2) Real.pi))
    have h₂ := min_le_right (δgL / 2) (min (δgR / 2) Real.pi)
    have h₃ := min_le_left (δgR / 2) Real.pi
    exact lt_of_le_of_lt
      (le_trans (min_le_right _ _) (le_trans h₁ (le_trans h₂ h₃))) (by linarith)
  have hrπ : r ≤ Real.pi := by
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))
  let xL := -Real.pi + r
  let xR := Real.pi - r
  have hxLopen : xL ∈ Set.Ioo (-Real.pi) Real.pi := by
    dsimp [xL]
    constructor
    · linarith
    · linarith [Real.pi_pos]
  have hxRopen : xR ∈ Set.Ioo (-Real.pi) Real.pi := by
    dsimp [xR]
    constructor <;> linarith [Real.pi_pos]
  have hxLclosed : xL ∈ Set.Icc (-Real.pi) Real.pi :=
    ⟨hxLopen.1.le, hxLopen.2.le⟩
  have hxRclosed : xR ∈ Set.Icc (-Real.pi) Real.pi :=
    ⟨hxRopen.1.le, hxRopen.2.le⟩
  have hdistL : dist xL (-Real.pi) = r := by
    rw [Real.dist_eq]
    dsimp [xL]
    simp [abs_of_pos hr]
  have hdistR : dist xR Real.pi = r := by
    rw [Real.dist_eq]
    dsimp [xR]
    simp [abs_of_pos hr]
  have hfLc : dist (f xL) (f (-Real.pi)) < ε := by
    exact hfL xL hxLclosed (hdistL.trans_lt hrfL)
  have hfRc : dist (f xR) (f Real.pi) < ε := by
    exact hfR xR hxRclosed (hdistR.trans_lt hrfR)
  have hgLc : dist (g xL) (g (-Real.pi)) < ε := by
    exact hgL (hdistL.trans_lt hrgL)
  have hgRc : dist (g xR) (g Real.pi) < ε := by
    exact hgR (hdistR.trans_lt hrgR)
  have huL : dist (g xL) (f xL) < ε := by
    simpa [g, Real.dist_eq] using hN N le_rfl xL hxLopen
  have huR : dist (g xR) (f xR) < ε := by
    simpa [g, Real.dist_eq] using hN N le_rfl xR hxRopen
  have ht₁ := dist_triangle (f (-Real.pi)) (f xL) (f Real.pi)
  have ht₂ := dist_triangle (f xL) (g xL) (f Real.pi)
  have ht₃ := dist_triangle (g xL) (g (-Real.pi)) (f Real.pi)
  have ht₄ := dist_triangle (g Real.pi) (g xR) (f Real.pi)
  have ht₅ := dist_triangle (g xR) (f xR) (f Real.pi)
  rw [hgend] at ht₃ hgLc
  rw [dist_comm] at hfLc huL hgRc
  dsimp [d, ε] at *
  linarith

/-- Source: `proof_gap/exercise_3134/4.txt`; integral form of the partial sum. -/
theorem gap4 (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (-Real.pi) Real.pi)) :
    ∀ n : ℕ, ∀ x : ℝ,
      partialSum f n x = partialSumIntegral f n x := by
  intro n x
  have hfu : ContinuousOn f (Set.uIcc (-Real.pi) Real.pi) := by
    simpa [Set.uIcc_of_le (by linarith [Real.pi_pos] :
      -Real.pi ≤ Real.pi)] using hf
  have hfint :
      IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi :=
    hfu.intervalIntegrable
  have hcosint (m : ℕ) :
      IntervalIntegrable
        (fun u => f u * Real.cos ((m : ℝ) * u))
        MeasureTheory.volume (-Real.pi) Real.pi :=
    (hfu.mul (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).continuousOn).intervalIntegrable
  have hsinint (m : ℕ) :
      IntervalIntegrable
        (fun u => f u * Real.sin ((m : ℝ) * u))
        MeasureTheory.volume (-Real.pi) Real.pi :=
    (hfu.mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).continuousOn).intervalIntegrable
  have hshiftint (m : ℕ) :
      IntervalIntegrable
        (fun u => f u * Real.cos ((m : ℝ) * (u - x)))
        MeasureTheory.volume (-Real.pi) Real.pi := by
    exact (hfu.mul (Real.continuous_cos.comp
      (continuous_const.mul
        (continuous_id.sub continuous_const))).continuousOn).intervalIntegrable
  have hshift (m : ℕ) :
      (∫ u in -Real.pi..Real.pi,
          f u * Real.cos ((m : ℝ) * (u - x))) =
        Real.cos ((m : ℝ) * x) *
            (∫ u in -Real.pi..Real.pi,
              f u * Real.cos ((m : ℝ) * u)) +
          Real.sin ((m : ℝ) * x) *
            (∫ u in -Real.pi..Real.pi,
              f u * Real.sin ((m : ℝ) * u)) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add
        ((hcosint m).const_mul _) ((hsinint m).const_mul _)]
    apply intervalIntegral.integral_congr
    intro u hu
    change
      f u * Real.cos ((m : ℝ) * (u - x)) =
        Real.cos ((m : ℝ) * x) *
            (f u * Real.cos ((m : ℝ) * u)) +
          Real.sin ((m : ℝ) * x) *
            (f u * Real.sin ((m : ℝ) * u))
    rw [mul_sub, Real.cos_sub]
    ring
  have hbase :
      IntervalIntegrable (fun u => f u * (1 / 2 : ℝ))
        MeasureTheory.volume (-Real.pi) Real.pi :=
    hfint.mul_const _
  have hsum :
      (∫ u in -Real.pi..Real.pi,
          f u * dirichletHalfKernel n (u - x)) =
        (∫ u in -Real.pi..Real.pi, f u * (1 / 2 : ℝ)) +
          ∑ m ∈ Finset.Icc 1 n,
            (∫ u in -Real.pi..Real.pi,
              f u * Real.cos ((m : ℝ) * (u - x))) := by
    unfold dirichletHalfKernel
    have hfun :
        (fun u : ℝ =>
          f u * (1 / 2 + ∑ m ∈ Finset.Icc 1 n,
            Real.cos ((m : ℝ) * (u - x)))) =
        (fun u => f u * (1 / 2 : ℝ) +
          ∑ m ∈ Finset.Icc 1 n,
            f u * Real.cos ((m : ℝ) * (u - x))) := by
      funext u
      rw [mul_add, Finset.mul_sum]
    rw [hfun]
    have hsumint :
        IntervalIntegrable
          (fun u => ∑ m ∈ Finset.Icc 1 n,
            f u * Real.cos ((m : ℝ) * (u - x)))
          MeasureTheory.volume (-Real.pi) Real.pi :=
      by
        have hi := IntervalIntegrable.sum (Finset.Icc 1 n)
          (fun m hm => hshiftint m)
        convert hi using 1
        funext u
        simp
    rw [intervalIntegral.integral_add hbase hsumint,
      intervalIntegral.integral_finset_sum]
    intro m hm
    exact hshiftint m
  unfold partialSum partialSumIntegral cosineCoefficient sineCoefficient
  rw [hsum, intervalIntegral.integral_mul_const]
  simp only [hshift]
  simp only [Nat.cast_zero]
  have hcos0 :
      (∫ u in -Real.pi..Real.pi, f u * Real.cos ((0 : ℝ) * u)) =
        ∫ u in -Real.pi..Real.pi, f u := by simp
  rw [hcos0]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro m hm
    ring

/--
Source: `proof_gap/exercise_3134/5.txt`; the quotient form excludes
the zeros of `sin(v/2)`.
-/
theorem gap5 :
    ∀ n : ℕ, ∀ v : ℝ, Real.sin (v / 2) ≠ 0 →
      dirichletHalfKernel n v = dirichletQuotient n v := by
  have hsucc (n : ℕ) (v : ℝ) :
      dirichletHalfKernel (n + 1) v =
        dirichletHalfKernel n v + Real.cos (((n + 1 : ℕ) : ℝ) * v) := by
    rw [dirichletHalfKernel, Finset.sum_Icc_succ_top (by omega)]
    unfold dirichletHalfKernel
    ring
  intro n
  induction n with
  | zero =>
      intro v hv
      simp [dirichletHalfKernel, dirichletQuotient]
      field_simp
  | succ n ih =>
      intro v hv
      rw [hsucc, ih v hv]
      unfold dirichletQuotient
      field_simp [hv]
      have hA :
          (2 * (n : ℝ) + 1) * v / 2 =
            ((n + 1 : ℕ) : ℝ) * v - v / 2 := by
        push_cast
        ring
      have hC :
          v * (2 * ((n + 1 : ℕ) : ℝ) + 1) / 2 =
            ((n + 1 : ℕ) : ℝ) * v + v / 2 := by
        push_cast
        ring
      rw [hA, hC, Real.sin_sub, Real.sin_add]
      ring

/-- Source: `proof_gap/exercise_3134/6.txt`; use a periodic representative. -/
theorem gap6 (f : ℝ → ℝ)
    (hf : Continuous f)
    (hper : Function.Periodic f (2 * Real.pi)) :
    ∀ n : ℕ, ∀ x : ℝ,
      partialSum f n x = symmetricPartialIntegral f n x := by
  intro n x
  rw [gap4 f hf.continuousOn n x]
  have hD : Continuous (dirichletHalfKernel n) := by
    unfold dirichletHalfKernel
    fun_prop
  let g : ℝ → ℝ := fun u =>
    f u * dirichletHalfKernel n (u - x)
  have hgper : Function.Periodic g (2 * Real.pi) := by
    intro u
    dsimp [g]
    rw [hper u]
    have harg : u + 2 * Real.pi - x = (u - x) + 2 * Real.pi := by ring
    rw [harg, dirichletHalfKernel_periodic n (u - x)]
  have hperiod :
      (∫ u in -Real.pi..Real.pi, g u) =
        ∫ u in x - Real.pi..x + Real.pi, g u := by
    have h := hgper.intervalIntegral_add_eq (-Real.pi) (x - Real.pi)
    convert h using 1 <;> ring
  have htranslate :
      (∫ u in x - Real.pi..x + Real.pi, g u) =
        ∫ t in -Real.pi..Real.pi,
          f (x + t) * dirichletHalfKernel n t := by
    calc
      (∫ u in x - Real.pi..x + Real.pi, g u) =
          ∫ t in -Real.pi..Real.pi, g (t + x) := by
        convert (intervalIntegral.integral_comp_add_right
          (a := -Real.pi) (b := Real.pi) g x).symm using 1 <;> ring
      _ = ∫ t in -Real.pi..Real.pi,
          f (x + t) * dirichletHalfKernel n t := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp [g]
        congr 2 <;> ring
  have hneg :
      (∫ t in -Real.pi..(0 : ℝ),
          f (x + t) * dirichletHalfKernel n t) =
        ∫ t in (0 : ℝ)..Real.pi,
          f (x - t) * dirichletHalfKernel n t := by
    calc
      (∫ t in -Real.pi..(0 : ℝ),
          f (x + t) * dirichletHalfKernel n t) =
          ∫ t in (0 : ℝ)..Real.pi,
            f (x + (-t)) * dirichletHalfKernel n (-t) := by
        simpa only [neg_zero] using (intervalIntegral.integral_comp_neg
          (f := fun t : ℝ =>
            f (x + t) * dirichletHalfKernel n t)
          (a := (0 : ℝ)) (b := Real.pi)).symm
      _ = ∫ t in (0 : ℝ)..Real.pi,
          f (x - t) * dirichletHalfKernel n t := by
        apply intervalIntegral.integral_congr
        intro t ht
        change
          f (x + (-t)) * dirichletHalfKernel n (-t) =
            f (x - t) * dirichletHalfKernel n t
        rw [dirichletHalfKernel_even]
        congr 2
  have hplusInt :
      IntervalIntegrable
        (fun t : ℝ => f (x + t) * dirichletHalfKernel n t)
        MeasureTheory.volume 0 Real.pi :=
    ((hf.comp (continuous_const.add continuous_id)).mul hD).intervalIntegrable _ _
  have hminusInt :
      IntervalIntegrable
        (fun t : ℝ => f (x - t) * dirichletHalfKernel n t)
        MeasureTheory.volume 0 Real.pi :=
    ((hf.comp (continuous_const.sub continuous_id)).mul hD).intervalIntegrable _ _
  have hsym :
      (∫ t in -Real.pi..Real.pi,
          f (x + t) * dirichletHalfKernel n t) =
        ∫ t in (0 : ℝ)..Real.pi,
          (f (x + t) + f (x - t)) *
            dirichletHalfKernel n t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (b := (0 : ℝ))]
    · rw [hneg, add_comm,
        ← intervalIntegral.integral_add hplusInt hminusInt]
      apply intervalIntegral.integral_congr
      intro t ht
      ring
    · have hc : Continuous
          (fun t : ℝ => f (x + t) * dirichletHalfKernel n t) :=
        (hf.comp (continuous_const.add continuous_id)).mul hD
      exact hc.intervalIntegrable _ _
    · exact hplusInt
  have hquot :
      (∫ t in (0 : ℝ)..Real.pi,
          (f (x + t) + f (x - t)) *
            dirichletHalfKernel n t) =
        ∫ t in (0 : ℝ)..Real.pi,
          (f (x + t) + f (x - t)) *
            (Real.sin (((n : ℝ) + 1 / 2) * t) /
              (2 * Real.sin (t / 2))) := by
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
    have ht' : t ∈ Set.Ioc (0 : ℝ) Real.pi := by
      simpa [Set.uIoc_of_le Real.pi_pos.le] using ht
    have hsin : Real.sin (t / 2) ≠ 0 := by
      have hspos : 0 < Real.sin (t / 2) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · exact half_pos ht'.1
        · have hhalf : t / 2 ≤ Real.pi / 2 := by linarith [ht'.2]
          linarith [Real.pi_pos]
      exact hspos.ne'
    change
      (f (x + t) + f (x - t)) * dirichletHalfKernel n t =
        (f (x + t) + f (x - t)) *
          (Real.sin (((n : ℝ) + 1 / 2) * t) /
            (2 * Real.sin (t / 2)))
    rw [gap5 n t hsin]
    unfold dirichletQuotient
    congr 3
    push_cast
    ring
  unfold partialSumIntegral symmetricPartialIntegral
  rw [show
      (∫ u in -Real.pi..Real.pi,
        f u * dirichletHalfKernel n (u - x)) =
      ∫ u in -Real.pi..Real.pi, g u by rfl,
    hperiod, htranslate, hsym, hquot]

private theorem symmetricPartialIntegral_halfKernel
    (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    symmetricPartialIntegral f n x =
      1 / Real.pi *
        ∫ t in (0 : ℝ)..Real.pi,
          (f (x + t) + f (x - t)) * dirichletHalfKernel n t := by
  unfold symmetricPartialIntegral
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
  have ht' : t ∈ Set.Ioc (0 : ℝ) Real.pi := by
    simpa [Set.uIoc_of_le Real.pi_pos.le] using ht
  have hsin : Real.sin (t / 2) ≠ 0 := by
    have hspos : 0 < Real.sin (t / 2) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · exact half_pos ht'.1
      · have hhalf : t / 2 ≤ Real.pi / 2 := by linarith [ht'.2]
        linarith [Real.pi_pos]
    exact hspos.ne'
  rw [gap5 n t hsin]
  unfold dirichletQuotient
  congr 3
  ring

private theorem fejerKernel_succ_sub_early (n : ℕ) (t : ℝ)
    (ht : Real.sin (t / 2) ≠ 0) :
    fejerKernel (n + 1) t - fejerKernel n t =
      2 * dirichletHalfKernel n t := by
  rw [gap5 n t ht]
  unfold fejerKernel dirichletQuotient
  field_simp [ht]
  let A : ℝ := ((n + 1 : ℕ) : ℝ) * t / 2
  let B : ℝ := (n : ℝ) * t / 2
  have hplus : t * (2 * (n : ℝ) + 1) / 2 = A + B := by
    dsimp [A, B]
    push_cast
    ring
  have hB : t * (n : ℝ) / 2 = B := by
    dsimp [B]
    ring
  have hminus : t / 2 = A - B := by
    dsimp [A, B]
    push_cast
    ring
  rw [hplus, hB, hminus, Real.sin_add, Real.sin_sub]
  have hA := Real.sin_sq_add_cos_sq A
  have hBs := Real.sin_sq_add_cos_sq B
  dsimp [A, B] at *
  nlinarith

private def fejerKernelProxyEarly (n : ℕ) (t : ℝ) : ℝ :=
  2 * ∑ k ∈ Finset.range n, dirichletHalfKernel k t

private theorem fejerKernel_eq_proxyEarly (n : ℕ) (t : ℝ)
    (ht0 : 0 < t) (htπ : t ≤ Real.pi) :
    fejerKernel n t = fejerKernelProxyEarly n t := by
  induction n with
  | zero => simp [fejerKernel, fejerKernelProxyEarly]
  | succ n ih =>
      have hsin : Real.sin (t / 2) ≠ 0 := by
        have : 0 < Real.sin (t / 2) := by
          apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
        exact this.ne'
      rw [fejerKernelProxyEarly, Finset.sum_range_succ]
      have hs := fejerKernel_succ_sub_early n t hsin
      unfold fejerKernelProxyEarly at ih
      linarith [hs, ih]

/-- Source: `proof_gap/exercise_3134/7.txt`; Cesàro average requires `n≥1`. -/
theorem gap7 (f : ℝ → ℝ) :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      fejerMean f n x =
        1 / (n : ℝ) * ∑ k ∈ Finset.range n, partialSum f k x := by
  intro n hn x
  simp [fejerMean, Nat.ne_of_gt hn]

/-- Source: `proof_gap/exercise_3134/8.txt`; Fejér-kernel integral formula. -/
theorem gap8 (f : ℝ → ℝ)
    (hf : Continuous f)
    (hper : Function.Periodic f (2 * Real.pi)) :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      fejerMean f n x = fejerIntegral f n x := by
  intro n hn x
  rw [gap7 f n hn x]
  simp_rw [gap6 f hf hper, symmetricPartialIntegral_halfKernel]
  let q : ℝ → ℝ := fun t => f (x + t) + f (x - t)
  have hq : Continuous q :=
    (hf.comp (continuous_const.add continuous_id)).add
      (hf.comp (continuous_const.sub continuous_id))
  have hterm (k : ℕ) :
      IntervalIntegrable
        (fun t => q t * dirichletHalfKernel k t)
        MeasureTheory.volume 0 Real.pi := by
    have hD : Continuous (dirichletHalfKernel k) := by
      unfold dirichletHalfKernel
      fun_prop
    exact (hq.mul hD).intervalIntegrable _ _
  have hInt :
      (∫ t in (0 : ℝ)..Real.pi, q t * fejerKernel n t) =
        2 * ∑ k ∈ Finset.range n,
          (∫ t in (0 : ℝ)..Real.pi,
            q t * dirichletHalfKernel k t) := by
    calc
      (∫ t in (0 : ℝ)..Real.pi, q t * fejerKernel n t) =
          ∫ t in (0 : ℝ)..Real.pi,
            q t * fejerKernelProxyEarly n t := by
        apply intervalIntegral.integral_congr_ae_restrict
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
        have ht' : t ∈ Set.Ioc (0 : ℝ) Real.pi := by
          simpa [Set.uIoc_of_le Real.pi_pos.le] using ht
        rw [fejerKernel_eq_proxyEarly n t ht'.1 ht'.2]
      _ = ∫ t in (0 : ℝ)..Real.pi,
          2 * (q t * ∑ k ∈ Finset.range n,
            dirichletHalfKernel k t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        unfold fejerKernelProxyEarly
        ring
      _ = 2 * ∫ t in (0 : ℝ)..Real.pi,
          q t * ∑ k ∈ Finset.range n,
            dirichletHalfKernel k t := by
        rw [intervalIntegral.integral_const_mul]
      _ = 2 * ∑ k ∈ Finset.range n,
          (∫ t in (0 : ℝ)..Real.pi,
            q t * dirichletHalfKernel k t) := by
        congr 1
        have hfun :
            (fun t : ℝ => q t * ∑ k ∈ Finset.range n,
              dirichletHalfKernel k t) =
              fun t => ∑ k ∈ Finset.range n,
                q t * dirichletHalfKernel k t := by
          funext t
          rw [Finset.mul_sum]
        rw [hfun, intervalIntegral.integral_finset_sum]
        intro k hk
        exact hterm k
  unfold fejerIntegral
  change
    1 / (n : ℝ) *
        ∑ k ∈ Finset.range n,
          (1 / Real.pi *
            ∫ t in (0 : ℝ)..Real.pi,
              q t * dirichletHalfKernel k t) =
      1 / (2 * (n : ℝ) * Real.pi) *
        ∫ t in (0 : ℝ)..Real.pi, q t * fejerKernel n t
  rw [hInt, Finset.mul_sum]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn0, Real.pi_ne_zero]
  ring_nf
  field_simp [hn0, Real.pi_ne_zero]
  have hden : (n : ℝ) * Real.pi ≠ 0 :=
    mul_ne_zero hn0 Real.pi_ne_zero
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hden]

private theorem fejerKernel_succ_sub (n : ℕ) (t : ℝ)
    (ht : Real.sin (t / 2) ≠ 0) :
    fejerKernel (n + 1) t - fejerKernel n t =
      2 * dirichletHalfKernel n t := by
  rw [gap5 n t ht]
  unfold fejerKernel dirichletQuotient
  field_simp [ht]
  let A : ℝ := ((n + 1 : ℕ) : ℝ) * t / 2
  let B : ℝ := (n : ℝ) * t / 2
  have hplus :
      t * (2 * (n : ℝ) + 1) / 2 = A + B := by
    dsimp [A, B]
    push_cast
    ring
  have hB : t * (n : ℝ) / 2 = B := by
    dsimp [B]
    ring
  have hminus : t / 2 = A - B := by
    dsimp [A, B]
    push_cast
    ring
  rw [hplus, hB, hminus, Real.sin_add, Real.sin_sub]
  have hA := Real.sin_sq_add_cos_sq A
  have hB := Real.sin_sq_add_cos_sq B
  dsimp [A, B] at *
  nlinarith

private theorem integral_cos_nat_pi (k : ℕ) (hk : k ≠ 0) :
    (∫ x in (0 : ℝ)..Real.pi, Real.cos ((k : ℝ) * x)) = 0 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hderiv (x : ℝ) :
      HasDerivAt
        (fun t : ℝ => Real.sin ((k : ℝ) * t) / (k : ℝ))
        (Real.cos ((k : ℝ) * x)) x := by
    simpa [hk'] using
      (((Real.hasDerivAt_sin ((k : ℝ) * x)).comp x
          ((hasDerivAt_id x).const_mul (k : ℝ))).div_const (k : ℝ))
  have hint :
      IntervalIntegrable (fun x : ℝ => Real.cos ((k : ℝ) * x))
        MeasureTheory.volume 0 Real.pi :=
    (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable 0 Real.pi
  have hs : Real.sin (Real.pi * (k : ℝ)) = 0 := by
    simpa [mul_comm] using Real.sin_nat_mul_pi k
  calc
    (∫ x in 0..Real.pi, Real.cos ((k : ℝ) * x)) =
        Real.sin ((k : ℝ) * Real.pi) / (k : ℝ) -
          Real.sin ((k : ℝ) * 0) / (k : ℝ) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hderiv x) hint
    _ = 0 := by
      rw [show (k : ℝ) * Real.pi = Real.pi * (k : ℝ) by ring, hs]
      simp

private theorem integral_dirichletHalfKernel (n : ℕ) :
    (∫ t in (0 : ℝ)..Real.pi, dirichletHalfKernel n t) =
      Real.pi / 2 := by
  unfold dirichletHalfKernel
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_finset_sum]
    · simp only [intervalIntegral.integral_const, sub_zero]
      have hsum :
          ∑ m ∈ Finset.Icc 1 n,
              (∫ t in (0 : ℝ)..Real.pi, Real.cos ((m : ℝ) * t)) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        exact integral_cos_nat_pi m
          (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)
      rw [hsum]
      simp [smul_eq_mul]
      ring
    · intro m hm
      exact (Real.continuous_cos.comp
        (continuous_const.mul continuous_id)).intervalIntegrable _ _
  · exact intervalIntegrable_const
  · exact (continuous_finset_sum _ fun m _ =>
      Real.continuous_cos.comp
        (continuous_const.mul continuous_id)).intervalIntegrable _ _

private theorem fejerKernel_integrable_and_integral :
    ∀ n : ℕ,
      IntervalIntegrable (fejerKernel n) MeasureTheory.volume 0 Real.pi ∧
        (∫ t in (0 : ℝ)..Real.pi, fejerKernel n t) =
          (n : ℝ) * Real.pi := by
  intro n
  induction n with
  | zero =>
      have hz : fejerKernel 0 = fun _ : ℝ => 0 := by
        funext t
        simp [fejerKernel]
      rw [hz]
      exact ⟨intervalIntegrable_const, by simp⟩
  | succ n ih =>
      have hae :
          fejerKernel (n + 1) =ᵐ[
            MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) Real.pi)]
            fun t => fejerKernel n t + 2 * dirichletHalfKernel n t := by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
        have htI : t ∈ Set.Icc (0 : ℝ) Real.pi := by
          have := Set.uIoc_subset_uIcc ht
          simpa [Set.uIcc_of_le Real.pi_pos.le] using this
        have hsin : Real.sin (t / 2) ≠ 0 := by
          have : 0 < Real.sin (t / 2) := by
            apply Real.sin_pos_of_pos_of_lt_pi
            · have htpos : 0 < t := by
                have ht' : t ∈ Set.Ioc (0 : ℝ) Real.pi := by
                  simpa [Set.uIoc_of_le Real.pi_pos.le] using ht
                exact ht'.1
              linarith
            · linarith [htI.2, Real.pi_pos]
          exact this.ne'
        linarith [fejerKernel_succ_sub n t hsin]
      have hD :
          IntervalIntegrable (fun t : ℝ => 2 * dirichletHalfKernel n t)
            MeasureTheory.volume 0 Real.pi := by
        exact (continuous_const.mul
          (continuous_const.add
            (continuous_finset_sum _ fun m _ =>
              Real.continuous_cos.comp
                (continuous_const.mul continuous_id)))).intervalIntegrable _ _
      have hrhs :
          IntervalIntegrable
            (fun t => fejerKernel n t + 2 * dirichletHalfKernel n t)
            MeasureTheory.volume 0 Real.pi :=
        ih.1.add hD
      have hsucc : IntervalIntegrable (fejerKernel (n + 1))
          MeasureTheory.volume 0 Real.pi :=
        hrhs.congr_ae hae.symm
      refine ⟨hsucc, ?_⟩
      rw [intervalIntegral.integral_congr_ae_restrict hae,
        intervalIntegral.integral_add ih.1 hD,
        intervalIntegral.integral_const_mul,
        integral_dirichletHalfKernel, ih.2]
      push_cast
      ring

private def fejerKernelProxy (n : ℕ) (t : ℝ) : ℝ :=
  2 * ∑ k ∈ Finset.range n, dirichletHalfKernel k t

private theorem fejerKernel_eq_proxy (n : ℕ) (t : ℝ)
    (ht0 : 0 < t) (htπ : t ≤ Real.pi) :
    fejerKernel n t = fejerKernelProxy n t := by
  induction n with
  | zero =>
      simp [fejerKernel, fejerKernelProxy]
  | succ n ih =>
      have hsin : Real.sin (t / 2) ≠ 0 := by
        have : 0 < Real.sin (t / 2) := by
          apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
        exact this.ne'
      rw [show n + 1 = Nat.succ n by rfl,
        fejerKernelProxy, Finset.sum_range_succ]
      have hs := fejerKernel_succ_sub n t hsin
      unfold fejerKernelProxy at ih
      rw [show Nat.succ n = n + 1 by omega]
      linarith [hs, ih]

private theorem fejerKernelProxy_continuous (n : ℕ) :
    Continuous (fejerKernelProxy n) := by
  unfold fejerKernelProxy dirichletHalfKernel
  fun_prop

private theorem continuous_mul_fejerKernel_intervalIntegrable
    (q : ℝ → ℝ) (hq : Continuous q) (n : ℕ) :
    IntervalIntegrable (fun t => q t * fejerKernel n t)
      MeasureTheory.volume 0 Real.pi := by
  have hp :
      IntervalIntegrable (fun t => q t * fejerKernelProxy n t)
        MeasureTheory.volume 0 Real.pi :=
    (hq.mul (fejerKernelProxy_continuous n)).intervalIntegrable _ _
  apply hp.congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
  have ht' : t ∈ Set.Ioc (0 : ℝ) Real.pi := by
    simpa [Set.uIoc_of_le Real.pi_pos.le] using ht
  rw [fejerKernel_eq_proxy n t ht'.1 ht'.2]

/-- Source: `proof_gap/exercise_3134/9.txt`; Fejér-kernel normalization. -/
theorem gap9 :
    ∀ n : ℕ, 1 ≤ n →
      1 =
        1 / ((n : ℝ) * Real.pi) *
          ∫ t in (0 : ℝ)..Real.pi, fejerKernel n t := by
  intro n hn
  rw [(fejerKernel_integrable_and_integral n).2]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn0, Real.pi_ne_zero]

/-- Source: `proof_gap/exercise_3134/10.txt`; subtract the normalized constant. -/
theorem gap10 (f : ℝ → ℝ)
    (hf : Continuous f)
    (hper : Function.Periodic f (2 * Real.pi)) :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      fejerMean f n x - f x = errorIntegral f n x := by
  intro n hn x
  rw [gap8 f hf hper n hn x]
  have hK := (fejerKernel_integrable_and_integral n).1
  have hA :
      IntervalIntegrable
        (fun t : ℝ => (f (x + t) + f (x - t)) * fejerKernel n t)
        MeasureTheory.volume 0 Real.pi := by
    apply continuous_mul_fejerKernel_intervalIntegrable
    exact (hf.comp (continuous_const.add continuous_id)).add
      (hf.comp (continuous_const.sub continuous_id))
  have hB :
      IntervalIntegrable
        (fun t : ℝ => (2 * f x) * fejerKernel n t)
        MeasureTheory.volume 0 Real.pi :=
    hK.const_mul _
  have herr :
      (∫ t in (0 : ℝ)..Real.pi,
          errorDifference f x t * fejerKernel n t) =
        (∫ t in (0 : ℝ)..Real.pi,
          (f (x + t) + f (x - t)) * fejerKernel n t) -
        (∫ t in (0 : ℝ)..Real.pi,
          (2 * f x) * fejerKernel n t) := by
    rw [← intervalIntegral.integral_sub hA hB]
    apply intervalIntegral.integral_congr
    intro t ht
    unfold errorDifference
    ring
  unfold fejerIntegral errorIntegral
  rw [herr, intervalIntegral.integral_const_mul,
    (fejerKernel_integrable_and_integral n).2]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn0, Real.pi_ne_zero]

/-- Source: `proof_gap/exercise_3134/11.txt`; boundedness is on the compact interval. -/
theorem gap11 (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (-Real.pi) Real.pi)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| ≤ M := by
  have hb : BddAbove ((fun x : ℝ => |f x|) '' Set.Icc (-Real.pi) Real.pi) :=
    isCompact_Icc.bddAbove_image hf.abs
  rcases hb with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  exact (hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)

/-- Source: `proof_gap/exercise_3134/12.txt`; uniform continuity on an inner interval. -/
theorem gap12 (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (-Real.pi) Real.pi)) :
    ∀ η : ℝ, 0 < η → η < Real.pi →
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ x' ∈ Set.Icc (-Real.pi + η / 2) (Real.pi - η / 2),
            ∀ x'' ∈ Set.Icc (-Real.pi + η / 2) (Real.pi - η / 2),
              |x' - x''| ≤ δ → |f x' - f x''| < ε / 2 := by
  intro η hη hηπ ε hε
  have hu : UniformContinuousOn f (Set.Icc (-Real.pi) Real.pi) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf
  rcases (Metric.uniformContinuousOn_iff.mp hu (ε / 2) (by positivity)) with
    ⟨δ, hδ, hcontrol⟩
  refine ⟨δ / 2, by positivity, ?_⟩
  intro x' hx' x'' hx'' hxx
  have hx'full : x' ∈ Set.Icc (-Real.pi) Real.pi := by
    constructor <;> linarith [hx'.1, hx'.2]
  have hx''full : x'' ∈ Set.Icc (-Real.pi) Real.pi := by
    constructor <;> linarith [hx''.1, hx''.2]
  have hd : dist x' x'' < δ := by
    rw [Real.dist_eq]
    exact lt_of_le_of_lt hxx (by linarith)
  simpa [Real.dist_eq] using hcontrol x' hx'full x'' hx''full hd

/-- Source: `proof_gap/exercise_3134/13.txt`; define the two integral pieces. -/
theorem gap13 (f : ℝ → ℝ) (n : ℕ) (x τ : ℝ)
    (hn : 1 ≤ n) (hτ0 : 0 ≤ τ) (hτπ : τ ≤ Real.pi)
    (hint :
      IntervalIntegrable
        (fun t : ℝ => errorDifference f x t * fejerKernel n t)
        MeasureTheory.volume 0 Real.pi) :
    errorIntegral f n x = nearError f n x τ + farError f n x τ := by
  unfold errorIntegral nearError farError
  rw [← mul_add]
  congr 1
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hint.mono_set (by
      rw [Set.uIcc_of_le hτ0, Set.uIcc_of_le Real.pi_pos.le]
      exact Set.Icc_subset_Icc_right hτπ))
    (hint.mono_set (by
      rw [Set.uIcc_of_le hτπ, Set.uIcc_of_le Real.pi_pos.le]
      exact Set.Icc_subset_Icc_left hτ0))).symm

/-- Source: `proof_gap/exercise_3134/14.txt`; the near piece uses uniform continuity. -/
theorem gap14 (f : ℝ → ℝ) (n : ℕ) (x τ ε : ℝ)
    (hn : 1 ≤ n) (hτ : 0 < τ) (hτπ : τ ≤ Real.pi) (hε : 0 < ε)
    (hnear :
      ∀ t ∈ Set.Icc (0 : ℝ) τ,
        |f (x + t) - f x| < ε / 2 ∧
        |f (x - t) - f x| < ε / 2) :
    |nearError f n x τ| < ε / 2 := by
  let g : ℝ → ℝ :=
    fun t => errorDifference f x t * fejerKernel n t
  let G : ℝ → ℝ := fun t => ε * fejerKernel n t
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hKnonneg (t : ℝ) : 0 ≤ fejerKernel n t := by
    unfold fejerKernel
    positivity
  have herr (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) τ) :
      |errorDifference f x t| < ε := by
    rcases hnear t ht with ⟨hp, hm⟩
    calc
      |errorDifference f x t| =
          |(f (x + t) - f x) + (f (x - t) - f x)| := by
            unfold errorDifference
            congr 1
            ring
      _ ≤ |f (x + t) - f x| + |f (x - t) - f x| :=
        abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hp hm
      _ = ε := by ring
  by_cases hg : IntervalIntegrable g MeasureTheory.volume 0 τ
  · have hG : IntervalIntegrable G MeasureTheory.volume 0 τ := by
      exact (((fejerKernel_integrable_and_integral n).1.mono_set (by
        rw [Set.uIcc_of_le hτ.le, Set.uIcc_of_le Real.pi_pos.le]
        exact Set.Icc_subset_Icc_right hτπ)).const_mul ε)
    have hle : (fun t => |g t|) ≤ᵐ[
        MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) τ)] G := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) τ := ⟨ht.1.le, ht.2⟩
      dsimp [g, G]
      rw [abs_mul, abs_of_nonneg (hKnonneg t)]
      exact mul_le_mul_of_nonneg_right (herr t ht').le (hKnonneg t)
    let ρ : ℝ := min τ (Real.pi / (n : ℝ))
    have hρ : 0 < ρ := by
      dsimp [ρ]
      positivity
    have hρτ : ρ ≤ τ := min_le_left _ _
    have hstrict :
        MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) τ)
          {t | |g t| < G t} ≠ 0 := by
      intro hz
      have hsub : Set.Ioc (0 : ℝ) ρ ⊆ {t | |g t| < G t} := by
        intro t ht
        have htτ : t ∈ Set.Icc (0 : ℝ) τ :=
          ⟨ht.1.le, ht.2.trans hρτ⟩
        have htpi : t ≤ Real.pi / (n : ℝ) :=
          ht.2.trans (min_le_right _ _)
        have hden : 0 < Real.sin (t / 2) := by
          apply Real.sin_pos_of_pos_of_lt_pi
          · exact half_pos ht.1
          · have := Real.pi_pos
            linarith [hτπ, htτ.2]
        have hnum : 0 < Real.sin ((n : ℝ) * t / 2) := by
          apply Real.sin_pos_of_pos_of_lt_pi
          · exact div_pos (mul_pos hnR ht.1) (by norm_num)
          · have hmul : (n : ℝ) * t ≤ Real.pi := by
              calc
                (n : ℝ) * t ≤ (n : ℝ) * (Real.pi / (n : ℝ)) :=
                  mul_le_mul_of_nonneg_left htpi hnR.le
                _ = Real.pi := by field_simp
            linarith [hmul, Real.pi_pos]
        have hKpos : 0 < fejerKernel n t := by
          unfold fejerKernel
          positivity
        dsimp [g, G]
        rw [abs_mul, abs_of_nonneg hKpos.le]
        exact mul_lt_mul_of_pos_right (herr t htτ) hKpos
      have hsub' :
          Set.Ioc (0 : ℝ) ρ ⊆
            Set.Ioc (0 : ℝ) τ ∩ {t | |g t| < G t} := by
        intro t ht
        exact ⟨⟨ht.1, ht.2.trans hρτ⟩, hsub ht⟩
      have hz' :
          MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) τ)
              (Set.Ioc (0 : ℝ) ρ) = 0 :=
        MeasureTheory.measure_mono_null hsub (hz)
      rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioc] at hz'
      have hinter :
          Set.Ioc (0 : ℝ) ρ ∩ Set.Ioc (0 : ℝ) τ =
            Set.Ioc (0 : ℝ) ρ := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Ioc]
        constructor
        · exact fun h => h.1
        · intro h
          exact ⟨h, h.1, h.2.trans hρτ⟩
      rw [hinter, Real.volume_Ioc] at hz'
      exact (not_le_of_gt hρ) (by simpa using hz')
    have hlt :
        (∫ t in (0 : ℝ)..τ, |g t|) <
          ∫ t in (0 : ℝ)..τ, G t := by
      exact intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOf_lt_ne_zero
        hτ.le hg.norm hG hle hstrict
    have hGmono :
        (∫ t in (0 : ℝ)..τ, G t) ≤
          ∫ t in (0 : ℝ)..Real.pi, G t := by
      apply intervalIntegral.integral_mono_interval le_rfl hτ.le hτπ
      · filter_upwards with t
        dsimp [G]
        exact mul_nonneg hε.le (hKnonneg t)
      · exact (fejerKernel_integrable_and_integral n).1.const_mul ε
    have habs :
        |∫ t in (0 : ℝ)..τ, g t| ≤ ∫ t in (0 : ℝ)..τ, |g t| := by
      simpa [← Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume)
          hτ.le
    have hcoef : 0 < 1 / (2 * (n : ℝ) * Real.pi) := by
      positivity
    unfold nearError
    change
      |1 / (2 * (n : ℝ) * Real.pi) *
          ∫ t in (0 : ℝ)..τ, g t| < ε / 2
    calc
      |1 / (2 * (n : ℝ) * Real.pi) *
          ∫ t in (0 : ℝ)..τ, g t| =
          (1 / (2 * (n : ℝ) * Real.pi)) *
            |∫ t in (0 : ℝ)..τ, g t| := by
              rw [abs_mul, abs_of_pos hcoef]
      _ ≤ (1 / (2 * (n : ℝ) * Real.pi)) *
          (∫ t in (0 : ℝ)..τ, |g t|) :=
        mul_le_mul_of_nonneg_left habs hcoef.le
      _ < (1 / (2 * (n : ℝ) * Real.pi)) *
          (∫ t in (0 : ℝ)..τ, G t) :=
        mul_lt_mul_of_pos_left hlt hcoef
      _ ≤ (1 / (2 * (n : ℝ) * Real.pi)) *
          (∫ t in (0 : ℝ)..Real.pi, G t) :=
        mul_le_mul_of_nonneg_left hGmono hcoef.le
      _ = ε / 2 := by
        dsimp [G]
        rw [intervalIntegral.integral_const_mul,
          (fejerKernel_integrable_and_integral n).2]
        field_simp [ne_of_gt hnR, Real.pi_ne_zero]
  · have hzero : (∫ t in (0 : ℝ)..τ, g t) = 0 := by
      rw [intervalIntegral.integral_undef hg]
    unfold nearError
    change
      |1 / (2 * (n : ℝ) * Real.pi) *
          ∫ t in (0 : ℝ)..τ, g t| < ε / 2
    rw [hzero]
    simp [hε]

/-- Source: `proof_gap/exercise_3134/15.txt`; quantitative far-tail bound. -/
theorem gap15 (f : ℝ → ℝ) (n : ℕ) (x τ M : ℝ)
    (hn : 1 ≤ n) (hτ : 0 < τ) (hτπ : τ < Real.pi)
    (hM : 0 ≤ M) (hbound : ∀ z : ℝ, |f z| ≤ M) :
    |farError f n x τ| ≤
      2 * M / ((n : ℝ) * Real.sin (τ / 2) ^ 2) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsτ : 0 < Real.sin (τ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact half_pos hτ
    · linarith [hτπ, Real.pi_pos]
  have hkernel :
      ∀ t ∈ Set.uIoc τ Real.pi,
        0 ≤ fejerKernel n t ∧
          fejerKernel n t ≤ 1 / Real.sin (τ / 2) ^ 2 := by
    intro t ht
    have ht' : t ∈ Set.Ioc τ Real.pi := by
      simpa [Set.uIoc_of_le hτπ.le] using ht
    have ht0 : 0 < t := hτ.trans ht'.1
    have hst : 0 < Real.sin (t / 2) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · exact half_pos ht0
      · linarith [ht'.2, Real.pi_pos]
    have hsinle : Real.sin (τ / 2) ≤ Real.sin (t / 2) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · linarith [Real.pi_pos]
      · linarith [ht'.2]
      · linarith [ht'.1]
    constructor
    · unfold fejerKernel
      positivity
    · unfold fejerKernel
      have hnum : |Real.sin ((n : ℝ) * t / 2)| ≤ 1 :=
        Real.abs_sin_le_one _
      have hquot :
          |Real.sin ((n : ℝ) * t / 2) / Real.sin (t / 2)| ≤
            1 / Real.sin (τ / 2) := by
        rw [abs_div, abs_of_pos hst]
        apply div_le_div₀ zero_le_one hnum hsτ hsinle
      have hright : 0 ≤ 1 / Real.sin (τ / 2) := by positivity
      simpa [abs_pow] using (sq_le_sq₀ (abs_nonneg _) hright).2 hquot
  have herr (t : ℝ) : |errorDifference f x t| ≤ 4 * M := by
    unfold errorDifference
    calc
      |f (x + t) - f x + f (x - t) - f x| ≤
          |f (x + t) - f x| + |f (x - t) - f x| := by
            simpa [sub_eq_add_neg, add_assoc] using
              abs_add_le (f (x + t) - f x) (f (x - t) - f x)
      _ ≤ (|f (x + t)| + |f x|) +
          (|f (x - t)| + |f x|) := by
            gcongr <;> exact abs_sub _ _
      _ ≤ 4 * M := by
            linarith [hbound (x + t), hbound x, hbound (x - t)]
  have hint :
      |∫ t in τ..Real.pi,
          errorDifference f x t * fejerKernel n t| ≤
        (4 * M / Real.sin (τ / 2) ^ 2) *
          |Real.pi - τ| := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hkernel t ht).1]
    have hk := (hkernel t ht).2
    have he := herr t
    have hs2 : 0 < Real.sin (τ / 2) ^ 2 := sq_pos_of_pos hsτ
    calc
      |errorDifference f x t| * fejerKernel n t ≤
          (4 * M) * (1 / Real.sin (τ / 2) ^ 2) :=
        mul_le_mul he hk (hkernel t ht).1 (by positivity)
      _ = 4 * M / Real.sin (τ / 2) ^ 2 := by ring
  unfold farError
  rw [abs_mul, abs_of_pos (by positivity :
    0 < 1 / (2 * (n : ℝ) * Real.pi))]
  have hlen : |Real.pi - τ| ≤ Real.pi := by
    rw [abs_of_nonneg (sub_nonneg.mpr hτπ.le)]
    linarith
  have hs2 : 0 < Real.sin (τ / 2) ^ 2 := sq_pos_of_pos hsτ
  calc
    1 / (2 * (n : ℝ) * Real.pi) *
        |∫ t in τ..Real.pi,
          errorDifference f x t * fejerKernel n t| ≤
      1 / (2 * (n : ℝ) * Real.pi) *
        ((4 * M / Real.sin (τ / 2) ^ 2) * |Real.pi - τ|) := by
          gcongr
    _ ≤ 1 / (2 * (n : ℝ) * Real.pi) *
        ((4 * M / Real.sin (τ / 2) ^ 2) * Real.pi) := by
          gcongr
    _ = 2 * M / ((n : ℝ) * Real.sin (τ / 2) ^ 2) := by
          field_simp [ne_of_gt hnR, Real.pi_ne_zero, ne_of_gt hs2]
          ring

/--
Source: `proof_gap/exercise_3134/17.txt`; matching endpoints yield a
continuous periodic extension, not continuity of the original partial-domain
function on all of `ℝ`.
-/
theorem gap17 (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (-Real.pi) Real.pi))
    (hend : f (-Real.pi) = f Real.pi) :
    HasContinuousPeriodicExtension f := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let G : AddCircle (2 * Real.pi) → ℝ :=
    AddCircle.liftIco (2 * Real.pi) (-Real.pi) f
  let F : ℝ → ℝ := fun x => G (x : AddCircle (2 * Real.pi))
  have hsum : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have hGc : Continuous G := by
    apply AddCircle.liftIco_continuous
    · simpa [hsum] using hend
    · simpa [hsum] using hf
  refine ⟨F, hGc.comp (AddCircle.continuous_mk' _), ?_, ?_⟩
  · intro x
    change G ((x + 2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) =
      G (x : AddCircle (2 * Real.pi))
    rw [AddCircle.coe_add_period]
  · intro x hx
    by_cases hxp : x = Real.pi
    · subst x
      change G (Real.pi : AddCircle (2 * Real.pi)) = f Real.pi
      have hcoe :
          (Real.pi : AddCircle (2 * Real.pi)) =
            ((-Real.pi : ℝ) : AddCircle (2 * Real.pi)) := by
        calc
          (Real.pi : AddCircle (2 * Real.pi)) =
              ((-Real.pi + 2 * Real.pi : ℝ) :
                AddCircle (2 * Real.pi)) :=
            congrArg (fun z : ℝ => (z : AddCircle (2 * Real.pi))) hsum.symm
          _ = ((-Real.pi : ℝ) : AddCircle (2 * Real.pi)) :=
            AddCircle.coe_add_period (2 * Real.pi) (-Real.pi)
      rw [hcoe]
      change AddCircle.liftIco (2 * Real.pi) (-Real.pi) f
        ((-Real.pi : ℝ) : AddCircle (2 * Real.pi)) = f Real.pi
      rw [AddCircle.liftIco_coe_apply]
      · exact hend
      · constructor
        · exact le_rfl
        · rw [hsum]
          linarith [Real.pi_pos]
    · change AddCircle.liftIco (2 * Real.pi) (-Real.pi) f
        (x : AddCircle (2 * Real.pi)) = f x
      rw [AddCircle.liftIco_coe_apply]
      exact ⟨hx.1, by rw [hsum]; exact lt_of_le_of_ne hx.2 hxp⟩

/-- Source: `proof_gap/exercise_3134/18.txt`; compact uniform continuity of the extension. -/
theorem gap18 (F : ℝ → ℝ)
    (hF : Continuous F)
    (hper : Function.Periodic F (2 * Real.pi)) :
    UniformContinuousOn F (Set.Icc (-2 * Real.pi) (2 * Real.pi)) := by
  exact isCompact_Icc.uniformContinuousOn_of_continuous hF.continuousOn

private theorem fejerMean_uniform_of_continuous_periodic
    (F : ℝ → ℝ) (hF : Continuous F)
    (hper : Function.Periodic F (2 * Real.pi)) :
    UniformConvergesOn (fejerMean F) F
      (Set.Icc (-Real.pi) Real.pi) := by
  intro ε hε
  have hu := gap18 F hF hper
  rcases (Metric.uniformContinuousOn_iff.mp hu (ε / 2) (by positivity)) with
    ⟨δ, hδ, hcontrol⟩
  let τ : ℝ := min (δ / 2) (Real.pi / 2)
  have hτ : 0 < τ := by
    dsimp [τ]
    positivity
  have hτπ : τ < Real.pi := by
    have := min_le_right (δ / 2) (Real.pi / 2)
    linarith [Real.pi_pos]
  have hs : 0 < Real.sin (τ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact half_pos hτ
    · linarith [hτπ, Real.pi_pos]
  have hb := hper.isBounded_of_continuous
    (mul_ne_zero two_ne_zero Real.pi_ne_zero) hF
  rcases Metric.isBounded_range_iff.mp hb with ⟨C, hC⟩
  let M : ℝ := max (C + |F 0|) 0
  have hM : 0 ≤ M := le_max_right _ _
  have hbound (z : ℝ) : |F z| ≤ M := by
    have hz := hC z 0
    rw [Real.dist_eq] at hz
    calc
      |F z| = |(F z - F 0) + F 0| := by congr 1 <;> ring
      _ ≤ |F z - F 0| + |F 0| := abs_add_le _ _
      _ ≤ C + |F 0| := by linarith
      _ ≤ M := le_max_left _ _
  obtain ⟨N₀ : ℕ, hN₀⟩ :=
    exists_nat_gt (4 * M / (ε * Real.sin (τ / 2) ^ 2))
  let N : ℕ := max 1 N₀
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hn1 : 1 ≤ n := (le_max_left 1 N₀).trans hn
  have hnN₀ : N₀ ≤ n := (le_max_right 1 N₀).trans hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hnq :
      4 * M / (ε * Real.sin (τ / 2) ^ 2) < (n : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hnN₀)
  have hnear :
      ∀ t ∈ Set.Icc (0 : ℝ) τ,
        |F (x + t) - F x| < ε / 2 ∧
        |F (x - t) - F x| < ε / 2 := by
    intro t ht
    have hxp : x + t ∈ Set.Icc (-2 * Real.pi) (2 * Real.pi) := by
      constructor <;> linarith [hx.1, hx.2, ht.1, ht.2, hτπ, Real.pi_pos]
    have hxm : x - t ∈ Set.Icc (-2 * Real.pi) (2 * Real.pi) := by
      constructor <;> linarith [hx.1, hx.2, ht.1, ht.2, hτπ, Real.pi_pos]
    have hx2 : x ∈ Set.Icc (-2 * Real.pi) (2 * Real.pi) := by
      constructor <;> linarith [hx.1, hx.2, Real.pi_pos]
    constructor
    · apply hcontrol (x + t) hxp x hx2
      rw [Real.dist_eq]
      have htδ : t < δ := by
        have := min_le_left (δ / 2) (Real.pi / 2)
        have htt : t ≤ δ / 2 := ht.2.trans (by simpa [τ] using this)
        linarith
      simpa [abs_of_nonneg ht.1] using htδ
    · apply hcontrol (x - t) hxm x hx2
      rw [Real.dist_eq]
      have htδ : t < δ := by
        have := min_le_left (δ / 2) (Real.pi / 2)
        have htt : t ≤ δ / 2 := ht.2.trans (by simpa [τ] using this)
        linarith
      have : |x - t - x| = t := by
        rw [show x - t - x = -t by ring, abs_neg, abs_of_nonneg ht.1]
      rw [this]
      exact htδ
  have hnearE :
      |nearError F n x τ| < ε / 2 :=
    gap14 F n x τ ε hn1 hτ hτπ.le hε hnear
  have hfarLe :
      |farError F n x τ| ≤
        2 * M / ((n : ℝ) * Real.sin (τ / 2) ^ 2) :=
    gap15 F n x τ M hn1 hτ hτπ hM hbound
  have hmul :
      4 * M <
        (n : ℝ) * (ε * Real.sin (τ / 2) ^ 2) := by
    exact (div_lt_iff₀ (mul_pos hε (sq_pos_of_pos hs))).mp hnq
  have hfarSmall :
      2 * M / ((n : ℝ) * Real.sin (τ / 2) ^ 2) < ε / 2 := by
    rw [div_lt_iff₀ (mul_pos hnR (sq_pos_of_pos hs))]
    nlinarith
  have hint :
      IntervalIntegrable
        (fun t : ℝ => errorDifference F x t * fejerKernel n t)
        MeasureTheory.volume 0 Real.pi := by
    apply continuous_mul_fejerKernel_intervalIntegrable
    unfold errorDifference
    fun_prop
  rw [gap10 F hF hper n hn1 x, gap13 F n x τ hn1 hτ.le hτπ.le hint]
  exact (abs_add_le _ _).trans_lt
    (by linarith [hnearE, hfarLe.trans_lt hfarSmall])

private theorem fejerMean_congr_Icc
    (f F : ℝ → ℝ)
    (hEq : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, F x = f x) :
    fejerMean F = fejerMean f := by
  have hcos (m : ℕ) : cosineCoefficient F m = cosineCoefficient f m := by
    unfold cosineCoefficient
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Set.Icc (-Real.pi) Real.pi := by
      simpa [Set.uIcc_of_le (by linarith [Real.pi_pos] :
        -Real.pi ≤ Real.pi)] using hu
    dsimp
    rw [hEq u hu']
  have hsin (m : ℕ) : sineCoefficient F m = sineCoefficient f m := by
    unfold sineCoefficient
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Set.Icc (-Real.pi) Real.pi := by
      simpa [Set.uIcc_of_le (by linarith [Real.pi_pos] :
        -Real.pi ≤ Real.pi)] using hu
    dsimp
    rw [hEq u hu']
  have hpartial (n : ℕ) : partialSum F n = partialSum f n := by
    funext x
    unfold partialSum
    rw [hcos]
    apply congrArg (fun z => cosineCoefficient f 0 / 2 + z)
    apply Finset.sum_congr rfl
    intro m hm
    rw [hcos, hsin]
  funext n x
  unfold fejerMean
  split_ifs
  · rw [hpartial]
  · congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [hpartial]

/-- Source: `proof_gap/exercise_3134/3.txt`; matching endpoints give global convergence. -/
theorem gap3 (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (-Real.pi) Real.pi))
    (hend : f (-Real.pi) = f Real.pi) :
    UniformConvergesOn (fejerMean f) f
      (Set.Icc (-Real.pi) Real.pi) := by
  rcases gap17 f hf hend with ⟨F, hF, hper, hEq⟩
  have hconv := fejerMean_uniform_of_continuous_periodic F hF hper
  rw [fejerMean_congr_Icc f F hEq] at hconv
  intro ε hε
  rcases hconv ε hε with ⟨N, hN⟩
  exact ⟨N, fun n hn x hx => by simpa [hEq x hx] using hN n hn x hx⟩

private theorem partialSum_eq_symmetric_of_periodization
    (f P : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (-Real.pi) Real.pi))
    (hper : Function.Periodic P (2 * Real.pi))
    (hEq :
      P =ᵐ[MeasureTheory.volume.restrict
        (Set.uIoc (-Real.pi) Real.pi)] f)
    (hPint : ∀ a b : ℝ,
      IntervalIntegrable P MeasureTheory.volume a b) :
    ∀ n x, partialSum f n x = symmetricPartialIntegral P n x := by
  intro n x
  rw [gap4 f hf n x]
  have hD : Continuous (dirichletHalfKernel n) := by
    unfold dirichletHalfKernel
    fun_prop
  have hbase :
      (∫ u in -Real.pi..Real.pi,
          f u * dirichletHalfKernel n (u - x)) =
        ∫ u in -Real.pi..Real.pi,
          P u * dirichletHalfKernel n (u - x) := by
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [hEq] with u hu
    rw [hu]
  let g : ℝ → ℝ := fun u =>
    P u * dirichletHalfKernel n (u - x)
  have hgper : Function.Periodic g (2 * Real.pi) := by
    intro u
    dsimp [g]
    rw [hper u]
    have harg : u + 2 * Real.pi - x = (u - x) + 2 * Real.pi := by ring
    rw [harg, dirichletHalfKernel_periodic n (u - x)]
  have hperiod :
      (∫ u in -Real.pi..Real.pi, g u) =
        ∫ u in x - Real.pi..x + Real.pi, g u := by
    have h := hgper.intervalIntegral_add_eq (-Real.pi) (x - Real.pi)
    convert h using 1 <;> ring
  have htranslate :
      (∫ u in x - Real.pi..x + Real.pi, g u) =
        ∫ t in -Real.pi..Real.pi,
          P (x + t) * dirichletHalfKernel n t := by
    calc
      (∫ u in x - Real.pi..x + Real.pi, g u) =
          ∫ t in -Real.pi..Real.pi, g (t + x) := by
        convert (intervalIntegral.integral_comp_add_right
          (a := -Real.pi) (b := Real.pi) g x).symm using 1 <;> ring
      _ = ∫ t in -Real.pi..Real.pi,
          P (x + t) * dirichletHalfKernel n t := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp [g]
        congr 2 <;> ring
  have hneg :
      (∫ t in -Real.pi..(0 : ℝ),
          P (x + t) * dirichletHalfKernel n t) =
        ∫ t in (0 : ℝ)..Real.pi,
          P (x - t) * dirichletHalfKernel n t := by
    calc
      (∫ t in -Real.pi..(0 : ℝ),
          P (x + t) * dirichletHalfKernel n t) =
          ∫ t in (0 : ℝ)..Real.pi,
            P (x + (-t)) * dirichletHalfKernel n (-t) := by
        simpa only [neg_zero] using (intervalIntegral.integral_comp_neg
          (f := fun t : ℝ =>
            P (x + t) * dirichletHalfKernel n t)
          (a := (0 : ℝ)) (b := Real.pi)).symm
      _ = ∫ t in (0 : ℝ)..Real.pi,
          P (x - t) * dirichletHalfKernel n t := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp
        rw [dirichletHalfKernel_even]
        congr 2
  have hplus0 :
      IntervalIntegrable (fun t : ℝ => P (x + t))
        MeasureTheory.volume 0 Real.pi := by
    have h := (hPint x (x + Real.pi)).comp_add_right x
    convert h using 1 <;> ring
  have hminus0 :
      IntervalIntegrable (fun t : ℝ => P (x - t))
        MeasureTheory.volume 0 Real.pi := by
    have h := ((hPint (x - Real.pi) x).comp_sub_left x).symm
    convert h using 1 <;> ring
  have hplusInt :
      IntervalIntegrable
        (fun t : ℝ => P (x + t) * dirichletHalfKernel n t)
        MeasureTheory.volume 0 Real.pi :=
    hplus0.mul_continuousOn hD.continuousOn
  have hminusInt :
      IntervalIntegrable
        (fun t : ℝ => P (x - t) * dirichletHalfKernel n t)
        MeasureTheory.volume 0 Real.pi :=
    hminus0.mul_continuousOn hD.continuousOn
  have hleftInt :
      IntervalIntegrable
        (fun t : ℝ => P (x + t) * dirichletHalfKernel n t)
        MeasureTheory.volume (-Real.pi) 0 := by
    have hp :
        IntervalIntegrable (fun t : ℝ => P (x + t))
          MeasureTheory.volume (-Real.pi) 0 := by
      have h := (hPint (x - Real.pi) x).comp_add_right x
      convert h using 1 <;> ring
    exact hp.mul_continuousOn hD.continuousOn
  have hsym :
      (∫ t in -Real.pi..Real.pi,
          P (x + t) * dirichletHalfKernel n t) =
        ∫ t in (0 : ℝ)..Real.pi,
          (P (x + t) + P (x - t)) *
            dirichletHalfKernel n t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (b := (0 : ℝ)) hleftInt hplusInt]
    rw [hneg, add_comm,
      ← intervalIntegral.integral_add hplusInt hminusInt]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have hquot :
      (∫ t in (0 : ℝ)..Real.pi,
          (P (x + t) + P (x - t)) *
            dirichletHalfKernel n t) =
        ∫ t in (0 : ℝ)..Real.pi,
          (P (x + t) + P (x - t)) *
            (Real.sin (((n : ℝ) + 1 / 2) * t) /
              (2 * Real.sin (t / 2))) := by
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
    have ht' : t ∈ Set.Ioc (0 : ℝ) Real.pi := by
      simpa [Set.uIoc_of_le Real.pi_pos.le] using ht
    have hsin : Real.sin (t / 2) ≠ 0 := by
      have hspos : 0 < Real.sin (t / 2) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · exact half_pos ht'.1
        · linarith [ht'.2, Real.pi_pos]
      exact hspos.ne'
    rw [gap5 n t hsin]
    unfold dirichletQuotient
    congr 3
    push_cast
    ring
  unfold partialSumIntegral symmetricPartialIntegral
  rw [hbase, show
      (∫ u in -Real.pi..Real.pi,
        P u * dirichletHalfKernel n (u - x)) =
      ∫ u in -Real.pi..Real.pi, g u by rfl,
    hperiod, htranslate, hsym, hquot]

private theorem intervalIntegrable_mul_fejerKernel
    (q : ℝ → ℝ)
    (hq : IntervalIntegrable q MeasureTheory.volume 0 Real.pi)
    (n : ℕ) :
    IntervalIntegrable (fun t => q t * fejerKernel n t)
      MeasureTheory.volume 0 Real.pi := by
  have hp :
      IntervalIntegrable (fun t => q t * fejerKernelProxy n t)
        MeasureTheory.volume 0 Real.pi :=
    hq.mul_continuousOn (fejerKernelProxy_continuous n).continuousOn
  apply hp.congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
  have ht' : t ∈ Set.Ioc (0 : ℝ) Real.pi := by
    simpa [Set.uIoc_of_le Real.pi_pos.le] using ht
  rw [fejerKernel_eq_proxy n t ht'.1 ht'.2]

private theorem fejerMean_eq_integral_of_periodization
    (f P : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (-Real.pi) Real.pi))
    (hper : Function.Periodic P (2 * Real.pi))
    (hEq :
      P =ᵐ[MeasureTheory.volume.restrict
        (Set.uIoc (-Real.pi) Real.pi)] f)
    (hPint : ∀ a b : ℝ,
      IntervalIntegrable P MeasureTheory.volume a b) :
    ∀ n, 1 ≤ n → ∀ x, fejerMean f n x = fejerIntegral P n x := by
  intro n hn x
  rw [gap7 f n hn x]
  simp_rw [partialSum_eq_symmetric_of_periodization f P hf hper hEq hPint,
    symmetricPartialIntegral_halfKernel]
  let q : ℝ → ℝ := fun t => P (x + t) + P (x - t)
  have hplus :
      IntervalIntegrable (fun t : ℝ => P (x + t))
        MeasureTheory.volume 0 Real.pi := by
    have h := (hPint x (x + Real.pi)).comp_add_right x
    convert h using 1 <;> ring
  have hminus :
      IntervalIntegrable (fun t : ℝ => P (x - t))
        MeasureTheory.volume 0 Real.pi := by
    have h := ((hPint (x - Real.pi) x).comp_sub_left x).symm
    convert h using 1 <;> ring
  have hq : IntervalIntegrable q MeasureTheory.volume 0 Real.pi :=
    hplus.add hminus
  have hterm (k : ℕ) :
      IntervalIntegrable
        (fun t => q t * dirichletHalfKernel k t)
        MeasureTheory.volume 0 Real.pi := by
    apply hq.mul_continuousOn
    unfold dirichletHalfKernel
    fun_prop
  have hInt :
      (∫ t in (0 : ℝ)..Real.pi, q t * fejerKernel n t) =
        2 * ∑ k ∈ Finset.range n,
          (∫ t in (0 : ℝ)..Real.pi,
            q t * dirichletHalfKernel k t) := by
    calc
      (∫ t in (0 : ℝ)..Real.pi, q t * fejerKernel n t) =
          ∫ t in (0 : ℝ)..Real.pi,
            q t * fejerKernelProxyEarly n t := by
        apply intervalIntegral.integral_congr_ae_restrict
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
        have ht' : t ∈ Set.Ioc (0 : ℝ) Real.pi := by
          simpa [Set.uIoc_of_le Real.pi_pos.le] using ht
        rw [fejerKernel_eq_proxyEarly n t ht'.1 ht'.2]
      _ = ∫ t in (0 : ℝ)..Real.pi,
          2 * (q t * ∑ k ∈ Finset.range n,
            dirichletHalfKernel k t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        unfold fejerKernelProxyEarly
        ring
      _ = 2 * ∫ t in (0 : ℝ)..Real.pi,
          q t * ∑ k ∈ Finset.range n,
            dirichletHalfKernel k t := by
        rw [intervalIntegral.integral_const_mul]
      _ = 2 * ∑ k ∈ Finset.range n,
          (∫ t in (0 : ℝ)..Real.pi,
            q t * dirichletHalfKernel k t) := by
        congr 1
        rw [show
          (fun t : ℝ => q t * ∑ k ∈ Finset.range n,
            dirichletHalfKernel k t) =
            fun t => ∑ k ∈ Finset.range n,
              q t * dirichletHalfKernel k t by
                funext t
                rw [Finset.mul_sum],
          intervalIntegral.integral_finset_sum]
        exact fun k hk => hterm k
  unfold fejerIntegral
  change
    1 / (n : ℝ) *
        ∑ k ∈ Finset.range n,
          (1 / Real.pi *
            ∫ t in (0 : ℝ)..Real.pi,
              q t * dirichletHalfKernel k t) =
      1 / (2 * (n : ℝ) * Real.pi) *
        ∫ t in (0 : ℝ)..Real.pi, q t * fejerKernel n t
  rw [hInt, Finset.mul_sum]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn0, Real.pi_ne_zero]
  ring_nf
  field_simp [hn0, Real.pi_ne_zero]
  have hden : (n : ℝ) * Real.pi ≠ 0 :=
    mul_ne_zero hn0 Real.pi_ne_zero
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hden]

private theorem fejerMean_sub_eq_error_of_periodization
    (f P : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (-Real.pi) Real.pi))
    (hper : Function.Periodic P (2 * Real.pi))
    (hEq :
      P =ᵐ[MeasureTheory.volume.restrict
        (Set.uIoc (-Real.pi) Real.pi)] f)
    (hPint : ∀ a b : ℝ,
      IntervalIntegrable P MeasureTheory.volume a b) :
    ∀ n, 1 ≤ n → ∀ x,
      fejerMean f n x - P x = errorIntegral P n x := by
  intro n hn x
  rw [fejerMean_eq_integral_of_periodization f P hf hper hEq hPint n hn x]
  have hplus :
      IntervalIntegrable (fun t : ℝ => P (x + t))
        MeasureTheory.volume 0 Real.pi := by
    have h := (hPint x (x + Real.pi)).comp_add_right x
    convert h using 1 <;> ring
  have hminus :
      IntervalIntegrable (fun t : ℝ => P (x - t))
        MeasureTheory.volume 0 Real.pi := by
    have h := ((hPint (x - Real.pi) x).comp_sub_left x).symm
    convert h using 1 <;> ring
  have hA := intervalIntegrable_mul_fejerKernel
    (fun t => P (x + t) + P (x - t)) (hplus.add hminus) n
  have hB :
      IntervalIntegrable
        (fun t : ℝ => (2 * P x) * fejerKernel n t)
        MeasureTheory.volume 0 Real.pi :=
    (fejerKernel_integrable_and_integral n).1.const_mul _
  have herr :
      (∫ t in (0 : ℝ)..Real.pi,
          errorDifference P x t * fejerKernel n t) =
        (∫ t in (0 : ℝ)..Real.pi,
          (P (x + t) + P (x - t)) * fejerKernel n t) -
        (∫ t in (0 : ℝ)..Real.pi,
          (2 * P x) * fejerKernel n t) := by
    rw [← intervalIntegral.integral_sub hA hB]
    apply intervalIntegral.integral_congr
    intro t ht
    unfold errorDifference
    ring
  unfold fejerIntegral errorIntegral
  rw [herr, intervalIntegral.integral_const_mul,
    (fejerKernel_integrable_and_integral n).2]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn0, Real.pi_ne_zero]

/-- Source: `proof_gap/exercise_3134/2.txt`; local Fejér convergence. -/
theorem gap2 (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (-Real.pi) Real.pi)) :
    ∀ η : ℝ, 0 < η → η < Real.pi →
      UniformConvergesOn (fejerMean f) f
        (Set.Icc (-Real.pi + η) (Real.pi - η)) := by
  intro η hη hηπ
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let G : AddCircle (2 * Real.pi) → ℝ :=
    AddCircle.liftIco (2 * Real.pi) (-Real.pi) f
  let P : ℝ → ℝ := fun x => G (x : AddCircle (2 * Real.pi))
  have hsum : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have hper : Function.Periodic P (2 * Real.pi) := by
    intro x
    change G ((x + 2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) =
      G (x : AddCircle (2 * Real.pi))
    rw [AddCircle.coe_add_period]
  have hEq :
      P =ᵐ[MeasureTheory.volume.restrict
        (Set.uIoc (-Real.pi) Real.pi)] f := by
    have hne :
        ∀ᵐ u ∂MeasureTheory.volume.restrict
          (Set.uIoc (-Real.pi) Real.pi), u ≠ Real.pi := by
      have hglobal : ∀ᵐ u ∂MeasureTheory.volume, u ≠ Real.pi := by
        simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
      exact hglobal.filter_mono
        (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)
    filter_upwards [
      MeasureTheory.ae_restrict_mem measurableSet_uIoc,
      hne] with u hu hupi
    have hu' : u ∈ Set.Ioc (-Real.pi) Real.pi := by
      simpa [Set.uIoc_of_le (by linarith [Real.pi_pos] :
        -Real.pi ≤ Real.pi)] using hu
    change AddCircle.liftIco (2 * Real.pi) (-Real.pi) f
      (u : AddCircle (2 * Real.pi)) = f u
    rw [AddCircle.liftIco_coe_apply]
    constructor
    · exact hu'.1.le
    · rw [hsum]
      exact lt_of_le_of_ne hu'.2 hupi
  have hfint :
      IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi := by
    have hfu : ContinuousOn f (Set.uIcc (-Real.pi) Real.pi) := by
      simpa [Set.uIcc_of_le (by linarith [Real.pi_pos] :
        -Real.pi ≤ Real.pi)] using hf
    exact hfu.intervalIntegrable
  have hPbase :
      IntervalIntegrable P MeasureTheory.volume (-Real.pi) Real.pi :=
    hfint.congr_ae hEq.symm
  have hPint : ∀ a b : ℝ,
      IntervalIntegrable P MeasureTheory.volume a b := by
    intro a b
    exact hper.intervalIntegrable
      (mul_ne_zero two_ne_zero Real.pi_ne_zero)
      (t := -Real.pi)
      (by convert hPbase using 1 <;> ring) a b
  rcases gap11 f hf with ⟨M, hM, hboundf⟩
  have hboundP (z : ℝ) : |P z| ≤ M := by
    let y : Set.Ico (-Real.pi) (-Real.pi + 2 * Real.pi) :=
      AddCircle.equivIco (2 * Real.pi) (-Real.pi)
        (z : AddCircle (2 * Real.pi))
    change |f y| ≤ M
    apply hboundf y
    constructor
    · exact y.property.1
    · exact y.property.2.le.trans_eq hsum
  intro ε hε
  rcases gap12 f hf η hη hηπ ε hε with
    ⟨δ, hδ, hcontrol⟩
  let τ : ℝ := min (δ / 2) (min (η / 2) (Real.pi / 2))
  have hτ : 0 < τ := by
    dsimp [τ]
    positivity
  have hτη : τ ≤ η / 2 := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hτπ : τ < Real.pi := by
    have := (min_le_right (δ / 2) (min (η / 2) (Real.pi / 2))).trans
      (min_le_right (η / 2) (Real.pi / 2))
    linarith [Real.pi_pos]
  have hs : 0 < Real.sin (τ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact half_pos hτ
    · linarith [hτπ, Real.pi_pos]
  obtain ⟨N₀ : ℕ, hN₀⟩ :=
    exists_nat_gt (4 * M / (ε * Real.sin (τ / 2) ^ 2))
  let N : ℕ := max 1 N₀
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hn1 : 1 ≤ n := (le_max_left 1 N₀).trans hn
  have hnN₀ : N₀ ≤ n := (le_max_right 1 N₀).trans hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hnq :
      4 * M / (ε * Real.sin (τ / 2) ^ 2) < (n : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hnN₀)
  have hPx : P x = f x := by
    change AddCircle.liftIco (2 * Real.pi) (-Real.pi) f
      (x : AddCircle (2 * Real.pi)) = f x
    rw [AddCircle.liftIco_coe_apply]
    constructor
    · linarith [hx.1]
    · rw [hsum]
      linarith [hx.2, hη]
  have hnear :
      ∀ t ∈ Set.Icc (0 : ℝ) τ,
        |P (x + t) - P x| < ε / 2 ∧
        |P (x - t) - P x| < ε / 2 := by
    intro t ht
    have hxpinner :
        x + t ∈ Set.Icc (-Real.pi + η / 2) (Real.pi - η / 2) := by
      constructor <;> linarith [hx.1, hx.2, ht.1, ht.2, hτη]
    have hxminner :
        x - t ∈ Set.Icc (-Real.pi + η / 2) (Real.pi - η / 2) := by
      constructor <;> linarith [hx.1, hx.2, ht.1, ht.2, hτη]
    have hxinner :
        x ∈ Set.Icc (-Real.pi + η / 2) (Real.pi - η / 2) := by
      constructor <;> linarith [hx.1, hx.2, hη]
    have hPplus : P (x + t) = f (x + t) := by
      change AddCircle.liftIco (2 * Real.pi) (-Real.pi) f
        ((x + t : ℝ) : AddCircle (2 * Real.pi)) = f (x + t)
      rw [AddCircle.liftIco_coe_apply]
      constructor
      · linarith [hxpinner.1, hη]
      · rw [hsum]
        linarith [hxpinner.2, hη]
    have hPminus : P (x - t) = f (x - t) := by
      change AddCircle.liftIco (2 * Real.pi) (-Real.pi) f
        ((x - t : ℝ) : AddCircle (2 * Real.pi)) = f (x - t)
      rw [AddCircle.liftIco_coe_apply]
      constructor
      · linarith [hxminner.1, hη]
      · rw [hsum]
        linarith [hxminner.2, hη]
    rw [hPplus, hPminus, hPx]
    apply And.intro
    · apply hcontrol (x + t) hxpinner x hxinner
      have htδ : t ≤ δ := by
        have htd2 : τ ≤ δ / 2 := min_le_left _ _
        linarith [ht.2]
      simpa [abs_of_nonneg ht.1] using htδ
    · apply hcontrol (x - t) hxminner x hxinner
      have htδ : t ≤ δ := by
        have htd2 : τ ≤ δ / 2 := min_le_left _ _
        linarith [ht.2]
      have habs : |x - t - x| = t := by
        rw [show x - t - x = -t by ring, abs_neg, abs_of_nonneg ht.1]
      rw [habs]
      exact htδ
  have hnearE :
      |nearError P n x τ| < ε / 2 :=
    gap14 P n x τ ε hn1 hτ hτπ.le hε hnear
  have hfarLe :
      |farError P n x τ| ≤
        2 * M / ((n : ℝ) * Real.sin (τ / 2) ^ 2) :=
    gap15 P n x τ M hn1 hτ hτπ hM hboundP
  have hmul :
      4 * M <
        (n : ℝ) * (ε * Real.sin (τ / 2) ^ 2) :=
    (div_lt_iff₀ (mul_pos hε (sq_pos_of_pos hs))).mp hnq
  have hfarSmall :
      2 * M / ((n : ℝ) * Real.sin (τ / 2) ^ 2) < ε / 2 := by
    rw [div_lt_iff₀ (mul_pos hnR (sq_pos_of_pos hs))]
    nlinarith
  have hplus :
      IntervalIntegrable (fun t : ℝ => P (x + t))
        MeasureTheory.volume 0 Real.pi := by
    have h := (hPint x (x + Real.pi)).comp_add_right x
    convert h using 1 <;> ring
  have hminus :
      IntervalIntegrable (fun t : ℝ => P (x - t))
        MeasureTheory.volume 0 Real.pi := by
    have h := ((hPint (x - Real.pi) x).comp_sub_left x).symm
    convert h using 1 <;> ring
  have hint :
      IntervalIntegrable
        (fun t : ℝ => errorDifference P x t * fejerKernel n t)
        MeasureTheory.volume 0 Real.pi := by
    apply intervalIntegrable_mul_fejerKernel
    convert
      (hplus.sub (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ => P x) MeasureTheory.volume 0 Real.pi)).add
      (hminus.sub (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ => P x) MeasureTheory.volume 0 Real.pi)) using 1
    funext t
    unfold errorDifference
    ring
  rw [← hPx,
    fejerMean_sub_eq_error_of_periodization f P hf hper hEq hPint n hn1 x,
    gap13 P n x τ hn1 hτ.le hτπ.le hint]
  exact (abs_add_le _ _).trans_lt
    (by linarith [hnearE, hfarLe.trans_lt hfarSmall])

/-- Source: `proof_gap/exercise_3134/16.txt`; explicit local uniform conclusion. -/
theorem gap16 (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (-Real.pi) Real.pi)) :
    ∀ η : ℝ, 0 < η → η < Real.pi →
      UniformConvergesOn (fejerMean f) f
        (Set.Icc (-Real.pi + η) (Real.pi - η)) := by
  exact gap2 f hf

/-- Source: `proof_gap/exercise_3134/19.txt`; global quantitative conclusion. -/
theorem gap19 (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (-Real.pi) Real.pi))
    (hend : f (-Real.pi) = f Real.pi) :
    UniformConvergesOn (fejerMean f) f
      (Set.Icc (-Real.pi) Real.pi) := by
  exact gap3 f hf hend

private theorem sawtooth_cosineCoefficient (m : ℕ) :
    cosineCoefficient (fun z : ℝ => z) m = 0 := by
  unfold cosineCoefficient
  by_cases hm : m = 0
  · subst m
    simp
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  let A : ℝ → ℝ := fun u =>
    u * Real.sin ((m : ℝ) * u) / (m : ℝ) +
      Real.cos ((m : ℝ) * u) / (m : ℝ) ^ 2
  have hA (u : ℝ) : HasDerivAt A (u * Real.cos ((m : ℝ) * u)) u := by
    dsimp [A]
    have hmul : HasDerivAt (fun v : ℝ => (m : ℝ) * v) (m : ℝ) u :=
      by
        convert (hasDerivAt_const u (m : ℝ)).mul (hasDerivAt_id u) using 1 <;>
          simp
    have hsin :
        HasDerivAt (fun v : ℝ => Real.sin ((m : ℝ) * v))
          (Real.cos ((m : ℝ) * u) * (m : ℝ)) u :=
      (Real.hasDerivAt_sin ((m : ℝ) * u)).comp u hmul
    have hcos :
        HasDerivAt (fun v : ℝ => Real.cos ((m : ℝ) * v))
          (-Real.sin ((m : ℝ) * u) * (m : ℝ)) u :=
      (Real.hasDerivAt_cos ((m : ℝ) * u)).comp u hmul
    convert
      ((((hasDerivAt_id u).mul hsin).div_const (m : ℝ)).add
        (hcos.div_const ((m : ℝ) ^ 2))) using 1 <;>
      simp only [id_eq] <;> field_simp [hmR] <;> ring
  have hint :
      IntervalIntegrable (fun u : ℝ => u * Real.cos ((m : ℝ) * u))
        MeasureTheory.volume (-Real.pi) Real.pi := by
    exact (continuous_id.mul (Real.continuous_cos.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _
  change 1 / Real.pi *
    (∫ u in -Real.pi..Real.pi, u * Real.cos ((m : ℝ) * u)) = 0
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hA u) hint]
  dsimp [A]
  rw [show (m : ℝ) * Real.pi = (m : ℕ) * Real.pi by rfl,
    Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  have hneg :
      (m : ℝ) * (-Real.pi) = -((m : ℕ) * Real.pi) := by ring
  rw [hneg, Real.sin_neg, Real.cos_neg, Real.sin_nat_mul_pi,
    Real.cos_nat_mul_pi]
  field_simp [hmR, Real.pi_ne_zero]
  ring

private theorem sawtooth_sineCoefficient (m : ℕ) (hm : m ≠ 0) :
    sineCoefficient (fun z : ℝ => z) m =
      2 * (-1 : ℝ) ^ (m + 1) / (m : ℝ) := by
  unfold sineCoefficient
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  let A : ℝ → ℝ := fun u =>
    -(u * Real.cos ((m : ℝ) * u) / (m : ℝ)) +
      Real.sin ((m : ℝ) * u) / (m : ℝ) ^ 2
  have hA (u : ℝ) : HasDerivAt A (u * Real.sin ((m : ℝ) * u)) u := by
    dsimp [A]
    have hmul : HasDerivAt (fun v : ℝ => (m : ℝ) * v) (m : ℝ) u :=
      by
        convert (hasDerivAt_const u (m : ℝ)).mul (hasDerivAt_id u) using 1 <;>
          simp
    have hsin :
        HasDerivAt (fun v : ℝ => Real.sin ((m : ℝ) * v))
          (Real.cos ((m : ℝ) * u) * (m : ℝ)) u :=
      (Real.hasDerivAt_sin ((m : ℝ) * u)).comp u hmul
    have hcos :
        HasDerivAt (fun v : ℝ => Real.cos ((m : ℝ) * v))
          (-Real.sin ((m : ℝ) * u) * (m : ℝ)) u :=
      (Real.hasDerivAt_cos ((m : ℝ) * u)).comp u hmul
    convert
      (((((hasDerivAt_id u).mul hcos).div_const (m : ℝ)).neg).add
        (hsin.div_const ((m : ℝ) ^ 2))) using 1 <;>
      simp only [id_eq] <;> field_simp [hmR] <;> ring
  have hint :
      IntervalIntegrable (fun u : ℝ => u * Real.sin ((m : ℝ) * u))
        MeasureTheory.volume (-Real.pi) Real.pi := by
    exact (continuous_id.mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _
  change 1 / Real.pi *
    (∫ u in -Real.pi..Real.pi, u * Real.sin ((m : ℝ) * u)) =
      2 * (-1 : ℝ) ^ (m + 1) / (m : ℝ)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hA u) hint]
  dsimp [A]
  rw [show (m : ℝ) * Real.pi = (m : ℕ) * Real.pi by rfl,
    Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  have hneg :
      (m : ℝ) * (-Real.pi) = -((m : ℕ) * Real.pi) := by ring
  rw [hneg, Real.sin_neg, Real.cos_neg, Real.sin_nat_mul_pi,
    Real.cos_nat_mul_pi]
  rw [show (-1 : ℝ) ^ (m + 1) = -((-1 : ℝ) ^ m) by
    rw [pow_succ]
    ring]
  field_simp [hmR, Real.pi_ne_zero]
  ring

private def alternatingSinSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n,
    (-1 : ℝ) ^ k * Real.sin (((k + 1 : ℕ) : ℝ) * x)

private theorem partialSum_sawtooth_succ (n : ℕ) (x : ℝ) :
    partialSum (fun z : ℝ => z) (n + 1) x =
      partialSum (fun z : ℝ => z) n x +
        2 * (-1 : ℝ) ^ n *
          Real.sin (((n + 1 : ℕ) : ℝ) * x) / (n + 1 : ℕ) := by
  unfold partialSum
  rw [Finset.sum_Icc_succ_top (by omega)]
  have hn1 : n + 1 ≠ 0 := by omega
  rw [sawtooth_cosineCoefficient, sawtooth_sineCoefficient (n + 1) hn1,
    sawtooth_cosineCoefficient]
  push_cast
  have hp : (-1 : ℝ) ^ (n + 1 + 1) = (-1 : ℝ) ^ n := by
    rw [show n + 1 + 1 = n + 2 by omega, pow_add]
    norm_num
  rw [hp]
  ring

private theorem partialSum_sawtooth_zero (x : ℝ) :
    partialSum (fun z : ℝ => z) 0 x = 0 := by
  unfold partialSum
  rw [sawtooth_cosineCoefficient]
  simp

private theorem sawtooth_partial_fejer_relation :
    ∀ n : ℕ, ∀ x : ℝ,
      (n : ℝ) * partialSum (fun z : ℝ => z) n x -
          ∑ k ∈ Finset.range n, partialSum (fun z : ℝ => z) k x =
        2 * alternatingSinSum n x := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [alternatingSinSum, partialSum_sawtooth_zero]
  | succ n ih =>
      intro x
      rw [Finset.sum_range_succ, alternatingSinSum,
        Finset.sum_range_succ, partialSum_sawtooth_succ]
      push_cast
      have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      field_simp [ne_of_gt hnpos]
      have h := ih x
      unfold alternatingSinSum at h
      push_cast at h
      ring_nf at h ⊢
      have hsum :
          ∑ k ∈ Finset.range n,
              Real.sin (x + x * (k : ℝ)) * (-1 : ℝ) ^ k =
            ∑ k ∈ Finset.range n,
              Real.sin ((k : ℝ) * x + x) * (-1 : ℝ) ^ k := by
        apply Finset.sum_congr rfl
        intro k hk
        congr 2
        ring
      rw [hsum]
      nlinarith [h]

private theorem partialSum_sub_fejerMean_sawtooth
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    partialSum (fun z : ℝ => z) n x -
        fejerMean (fun z : ℝ => z) n x =
      2 / (n : ℝ) * alternatingSinSum n x := by
  rw [gap7 (fun z : ℝ => z) n hn x]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have h := sawtooth_partial_fejer_relation n x
  field_simp [hnR]
  nlinarith

private theorem alternatingSinSum_identity :
    ∀ n : ℕ, ∀ x : ℝ,
      2 * Real.cos (x / 2) * alternatingSinSum n x =
        Real.sin (x / 2) +
          (-1 : ℝ) ^ (n + 1) *
            Real.sin (((n : ℝ) + 1 / 2) * x) := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [alternatingSinSum]
      congr 1
      ring
  | succ n ih =>
      intro x
      rw [alternatingSinSum, Finset.sum_range_succ]
      unfold alternatingSinSum at ih
      have htrig :
          2 * Real.cos (x / 2) *
              Real.sin ((((n + 1 : ℕ) : ℝ)) * x) =
            Real.sin (((n : ℝ) + 3 / 2) * x) +
              Real.sin (((n : ℝ) + 1 / 2) * x) := by
        push_cast
        have ha :
            ((n : ℝ) + 3 / 2) * x =
              ((n : ℝ) + 1) * x + x / 2 := by ring
        have hb :
            ((n : ℝ) + 1 / 2) * x =
              ((n : ℝ) + 1) * x - x / 2 := by ring
        rw [ha, hb, Real.sin_add, Real.sin_sub]
        ring
      have hp : (-1 : ℝ) ^ (n + 1 + 1) = -((-1 : ℝ) ^ (n + 1)) := by
        rw [pow_succ]
        ring
      have hp' : (-1 : ℝ) ^ (n + 1) = -((-1 : ℝ) ^ n) := by
        rw [pow_succ]
        ring
      have htrig' :
          2 * Real.cos (x / 2) *
              Real.sin (((n : ℝ) + 1) * x) =
            Real.sin (((n : ℝ) + 3 / 2) * x) +
              Real.sin (((n : ℝ) + 1 / 2) * x) := by
        simpa only [Nat.cast_add, Nat.cast_one] using htrig
      have hlast :
          (((n + 1 : ℕ) : ℝ) + 1 / 2) * x =
            ((n : ℝ) + 3 / 2) * x := by
        push_cast
        ring
      calc
        2 * Real.cos (x / 2) *
              (∑ k ∈ Finset.range n,
                (-1 : ℝ) ^ k * Real.sin (((k + 1 : ℕ) : ℝ) * x) +
                (-1 : ℝ) ^ n * Real.sin (((n + 1 : ℕ) : ℝ) * x)) =
            Real.sin (x / 2) +
              (-1 : ℝ) ^ (n + 1) *
                Real.sin (((n : ℝ) + 1 / 2) * x) +
              (-1 : ℝ) ^ n *
                (2 * Real.cos (x / 2) *
                  Real.sin (((n : ℝ) + 1) * x)) := by
                    rw [mul_add, ih x]
                    push_cast
                    ring
        _ = Real.sin (x / 2) +
              (-1 : ℝ) ^ (n + 1 + 1) *
                Real.sin ((((n + 1 : ℕ) : ℝ) + 1 / 2) * x) := by
                    rw [htrig', hp, hp', hlast]
                    ring

private theorem alternatingSinSum_bound (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Ioo (-Real.pi) Real.pi) :
    |alternatingSinSum n x| ≤ 1 / Real.cos (x / 2) := by
  have hc : 0 < Real.cos (x / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [hx.1, hx.2]
  have hid := alternatingSinSum_identity n x
  have hrhs :
      |Real.sin (x / 2) +
          (-1 : ℝ) ^ (n + 1) *
            Real.sin (((n : ℝ) + 1 / 2) * x)| ≤ 2 := by
    calc
      |_ + _| ≤ |Real.sin (x / 2)| +
          |(-1 : ℝ) ^ (n + 1) *
            Real.sin (((n : ℝ) + 1 / 2) * x)| := abs_add_le _ _
      _ = |Real.sin (x / 2)| +
          |Real.sin (((n : ℝ) + 1 / 2) * x)| := by
            rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      _ ≤ 2 := by
        linarith [Real.abs_sin_le_one (x / 2),
          Real.abs_sin_le_one (((n : ℝ) + 1 / 2) * x)]
  rw [← hid, abs_mul, abs_mul, abs_of_pos hc] at hrhs
  apply (le_div_iff₀ hc).2
  norm_num at hrhs
  nlinarith [abs_nonneg (alternatingSinSum n x)]

/-- Source: `proof_gap/exercise_3134/20.txt`; Fourier sums of the sawtooth. -/
theorem gap20 :
    ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      Tendsto (fun n : ℕ => partialSum (fun z : ℝ => z) n x) atTop
        (𝓝 (sawtoothLimit x)) := by
  intro x hx
  by_cases hep : x = -Real.pi ∨ x = Real.pi
  · have hzero (n : ℕ) :
        partialSum (fun z : ℝ => z) n x = 0 := by
      unfold partialSum
      rw [sawtooth_cosineCoefficient]
      simp only [zero_div, zero_add]
      apply Finset.sum_eq_zero
      intro m hm
      rw [sawtooth_cosineCoefficient]
      simp only [zero_mul, zero_add]
      rcases hep with hL | hR
      · subst x
        rw [mul_neg, Real.sin_neg]
        have hs : Real.sin ((m : ℝ) * Real.pi) = 0 := by
          simpa using Real.sin_nat_mul_pi m
        rw [hs, neg_zero, mul_zero]
      · subst x
        have hs : Real.sin ((m : ℝ) * Real.pi) = 0 := by
          simpa using Real.sin_nat_mul_pi m
        rw [hs, mul_zero]
    have hlim : sawtoothLimit x = 0 := by simp [sawtoothLimit, hep]
    rw [hlim]
    have hfun :
        (fun n : ℕ => partialSum (fun z : ℝ => z) n x) =
          fun _ : ℕ => 0 := by
      funext n
      exact hzero n
    rw [hfun]
    exact tendsto_const_nhds
  · have hxopen : x ∈ Set.Ioo (-Real.pi) Real.pi :=
      ⟨lt_of_le_of_ne hx.1 (by
        intro h
        exact hep (Or.inl h.symm)),
       lt_of_le_of_ne hx.2 (by
         intro h
         exact hep (Or.inr h))⟩
    have habs : |x| < Real.pi := (abs_lt).2 hxopen
    let η : ℝ := (Real.pi - |x|) / 2
    have hη : 0 < η := by
      dsimp [η]
      linarith
    have hηπ : η < Real.pi := by
      dsimp [η]
      have hnonneg := abs_nonneg x
      linarith [Real.pi_pos]
    have hxinner :
        x ∈ Set.Icc (-Real.pi + η) (Real.pi - η) := by
      dsimp [η]
      constructor
      · have hnegabs : -|x| ≤ x := neg_abs_le x
        linarith
      · have habsle : x ≤ |x| := le_abs_self x
        linarith
    have hfejerU := gap2 (fun z : ℝ => z) continuousOn_id η hη hηπ
    have hlimit : sawtoothLimit x = x := by simp [sawtoothLimit, hep]
    rw [hlimit]
    refine Metric.tendsto_atTop.mpr ?_
    intro ε hε
    rcases hfejerU (ε / 2) (by positivity) with ⟨N₁, hN₁⟩
    have hc : 0 < Real.cos (x / 2) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith [hxopen.1, hxopen.2]
    obtain ⟨N₂ : ℕ, hN₂⟩ :=
      exists_nat_gt (4 / (ε * Real.cos (x / 2)))
    let N : ℕ := max 1 (max N₁ N₂)
    refine ⟨N, ?_⟩
    intro n hn
    have hn1 : 1 ≤ n := (le_max_left 1 (max N₁ N₂)).trans hn
    have hnN₁ : N₁ ≤ n :=
      (le_max_left N₁ N₂).trans
        ((le_max_right 1 (max N₁ N₂)).trans hn)
    have hnN₂ : N₂ ≤ n :=
      (le_max_right N₁ N₂).trans
        ((le_max_right 1 (max N₁ N₂)).trans hn)
    have hnR : 0 < (n : ℝ) := by exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one hn1)
    have hA := alternatingSinSum_bound n x hxopen
    have hdiff :
        |partialSum (fun z : ℝ => z) n x -
            fejerMean (fun z : ℝ => z) n x| < ε / 2 := by
      rw [partialSum_sub_fejerMean_sawtooth n hn1 x,
        abs_mul, abs_of_pos (div_pos two_pos hnR)]
      have hle :
          2 / (n : ℝ) * |alternatingSinSum n x| ≤
            2 / (n : ℝ) * (1 / Real.cos (x / 2)) :=
        mul_le_mul_of_nonneg_left hA (div_pos two_pos hnR).le
      have hnq :
          4 / (ε * Real.cos (x / 2)) < (n : ℝ) :=
        hN₂.trans_le (by exact_mod_cast hnN₂)
      have hmul :
          4 < (n : ℝ) * (ε * Real.cos (x / 2)) := by
        exact (div_lt_iff₀ (mul_pos hε hc)).mp hnq
      calc
        2 / (n : ℝ) * |alternatingSinSum n x| ≤
            2 / (n : ℝ) * (1 / Real.cos (x / 2)) := hle
        _ < ε / 2 := by
          rw [div_mul_div_comm, div_lt_iff₀ (mul_pos hnR hc)]
          nlinarith
    have hfejer := hN₁ n hnN₁ x hxinner
    rw [Real.dist_eq]
    calc
      |partialSum (fun z : ℝ => z) n x - x| ≤
          |partialSum (fun z : ℝ => z) n x -
            fejerMean (fun z : ℝ => z) n x| +
          |fejerMean (fun z : ℝ => z) n x - x| := by
            convert abs_add_le
              (partialSum (fun z : ℝ => z) n x -
                fejerMean (fun z : ℝ => z) n x)
              (fejerMean (fun z : ℝ => z) n x - x) using 1 <;> ring
      _ < ε := by linarith

/-- Source: `proof_gap/exercise_3134/21.txt`; make the endpoint cases explicit. -/
theorem gap21 :
    ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      sawtoothLimit x =
        if x = -Real.pi ∨ x = Real.pi then 0 else x := by
  intro x hx
  rfl

/-- Source: `proof_gap/exercise_3134/22.txt`; pointwise Fejér limit. -/
theorem gap22 :
    ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      Tendsto (fun n : ℕ => fejerMean (fun z : ℝ => z) n x) atTop
        (𝓝 (sawtoothLimit x)) := by
  intro x hx
  have hc := (gap20 x hx).cesaro
  apply hc.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp [fejerMean, Nat.ne_of_gt hn, one_div]

/-- Source: `proof_gap/exercise_3134/23.txt`; the assumed open-interval uniform limit. -/
theorem gap23
    (h :
      UniformConvergesOn (fejerMean (fun z : ℝ => z)) (fun z : ℝ => z)
        (Set.Ioo (-Real.pi) Real.pi)) :
    UniformConvergesOn (fejerMean (fun z : ℝ => z)) sawtoothLimit
      (Set.Icc (-Real.pi) Real.pi) := by
  intro ε hε
  rcases h ε hε with ⟨N, hN⟩
  have hLm : -Real.pi ∈ Set.Icc (-Real.pi) Real.pi :=
    ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hRm : Real.pi ∈ Set.Icc (-Real.pi) Real.pi :=
    ⟨by linarith [Real.pi_pos], le_rfl⟩
  rcases Metric.tendsto_atTop.mp (gap22 (-Real.pi) hLm) ε hε with
    ⟨NL, hNL⟩
  rcases Metric.tendsto_atTop.mp (gap22 Real.pi hRm) ε hε with
    ⟨NR, hNR⟩
  refine ⟨max N (max NL NR), ?_⟩
  intro n hn x hx
  by_cases hxl : x = -Real.pi
  · subst x
    simpa [Real.dist_eq, abs_sub_comm] using
      hNL n (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn))
  by_cases hxr : x = Real.pi
  · subst x
    simpa [Real.dist_eq, abs_sub_comm] using
      hNR n (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) hn))
  have hxopen : x ∈ Set.Ioo (-Real.pi) Real.pi :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hxl), lt_of_le_of_ne hx.2 hxr⟩
  simpa [sawtoothLimit, hxl, hxr] using
    hN n (le_trans (le_max_left _ _) hn) x hxopen

/-- Source: `proof_gap/exercise_3134/24.txt`; a uniform limit of continuous means is continuous. -/
theorem gap24
    (hcont :
      ∀ n : ℕ,
        ContinuousOn (fejerMean (fun z : ℝ => z) n)
          (Set.Icc (-Real.pi) Real.pi))
    (hunif :
      UniformConvergesOn (fejerMean (fun z : ℝ => z)) sawtoothLimit
        (Set.Icc (-Real.pi) Real.pi)) :
    ContinuousOn sawtoothLimit (Set.Icc (-Real.pi) Real.pi) := by
  have ht :
      TendstoUniformlyOn (fejerMean (fun z : ℝ => z)) sawtoothLimit atTop
        (Set.Icc (-Real.pi) Real.pi) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    rcases hunif ε hε with ⟨N, hN⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    intro x hx
    simpa [Real.dist_eq, abs_sub_comm] using hN n hn x hx
  exact ht.continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall hcont))

/-- Source: `proof_gap/exercise_3134/25.txt`; right endpoint discontinuity. -/
theorem gap25 : ¬ContinuousAt sawtoothLimit Real.pi := by
  intro h
  rcases (Metric.continuousAt_iff.mp h (Real.pi / 2) (by positivity)) with
    ⟨δ, hδ, hcontrol⟩
  let r : ℝ := min (δ / 2) (Real.pi / 2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrδ : r < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrπ : r ≤ Real.pi / 2 := min_le_right _ _
  have hnep : Real.pi - r ≠ Real.pi := by linarith
  have hnen : Real.pi - r ≠ -Real.pi := by
    intro heq
    have : Real.pi - r > 0 := by linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have hsaw : sawtoothLimit (Real.pi - r) = Real.pi - r := by
    simp [sawtoothLimit, hnen, hnep]
  have hsawpi : sawtoothLimit Real.pi = 0 := by simp [sawtoothLimit]
  have hd : dist (Real.pi - r) Real.pi < δ := by
    rw [Real.dist_eq]
    simp [abs_of_pos hr]
    exact hrδ
  have hout := hcontrol hd
  rw [hsaw, hsawpi, Real.dist_eq, sub_zero, abs_of_pos (by linarith [Real.pi_pos])] at hout
  linarith

/-- Source: `proof_gap/exercise_3134/26.txt`; left endpoint discontinuity. -/
theorem gap26 : ¬ContinuousAt sawtoothLimit (-Real.pi) := by
  intro h
  rcases (Metric.continuousAt_iff.mp h (Real.pi / 2) (by positivity)) with
    ⟨δ, hδ, hcontrol⟩
  let r : ℝ := min (δ / 2) (Real.pi / 2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrδ : r < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrπ : r ≤ Real.pi / 2 := min_le_right _ _
  have hnen : -Real.pi + r ≠ -Real.pi := by linarith
  have hnep : -Real.pi + r ≠ Real.pi := by
    intro heq
    have : -Real.pi + r < 0 := by linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have hsaw : sawtoothLimit (-Real.pi + r) = -Real.pi + r := by
    simp [sawtoothLimit, hnen, hnep]
  have hsawn : sawtoothLimit (-Real.pi) = 0 := by simp [sawtoothLimit]
  have hd : dist (-Real.pi + r) (-Real.pi) < δ := by
    rw [Real.dist_eq]
    simp [abs_of_pos hr]
    exact hrδ
  have hout := hcontrol hd
  rw [hsaw, hsawn, Real.dist_eq, sub_zero,
    abs_of_nonpos (by linarith [Real.pi_pos])] at hout
  linarith

/-- Source: `proof_gap/exercise_3134/27.txt`; contradiction for the sawtooth. -/
theorem gap27 :
    UniformConvergesOn (fejerMean (fun z : ℝ => z)) (fun z : ℝ => z)
      (Set.Ioo (-Real.pi) Real.pi) → False := by
  intro h
  exact gap1 (fun z : ℝ => z) continuous_id.continuousOn
    (by linarith [Real.pi_pos]) h

/-- Source: `proof_gap/exercise_3134/28.txt`; corrected complete Fejér conclusion. -/
theorem gap28 (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (-Real.pi) Real.pi)) :
    (∀ η : ℝ, 0 < η → η < Real.pi →
      UniformConvergesOn (fejerMean f) f
        (Set.Icc (-Real.pi + η) (Real.pi - η))) ∧
    (f (-Real.pi) = f Real.pi →
      UniformConvergesOn (fejerMean f) f
        (Set.Icc (-Real.pi) Real.pi)) := by
  exact ⟨gap2 f hf, gap3 f hf⟩

end

end ProofGap.Exercise3134
