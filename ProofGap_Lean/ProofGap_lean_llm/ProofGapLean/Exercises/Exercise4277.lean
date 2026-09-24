import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4277

noncomputable section

open scoped Interval

abbrev Point := ℝ × ℝ

def speed (γ : ℝ → Point) (t : ℝ) : ℝ :=
  Real.sqrt
    (deriv (fun s => (γ s).1) t ^ 2 + deriv (fun s => (γ s).2) t ^ 2)

def lineIntegral (P Q : Point → ℝ) (γ : ℝ → Point) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    P (γ t) * deriv (fun s => (γ s).1) t +
      Q (γ t) * deriv (fun s => (γ s).2) t

def projectedIntegral
    (P Q : Point → ℝ) (γ : ℝ → Point) (α : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    (P (γ t) * Real.cos (α t) + Q (γ t) * Real.sin (α t)) *
      speed γ t

def absoluteProjectedIntegral
    (P Q : Point → ℝ) (γ : ℝ → Point) (α : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    |P (γ t) * Real.cos (α t) + Q (γ t) * Real.sin (α t)| *
      speed γ t

def arcLength (γ : ℝ → Point) : ℝ :=
  ∫ t in (0 : ℝ)..1, speed γ t

def HasTangentAngle (γ : ℝ → Point) (α : ℝ → ℝ) : Prop :=
  ∀ t, t ∈ Set.Icc (0 : ℝ) 1 →
    deriv (fun s => (γ s).1) t = speed γ t * Real.cos (α t) ∧
      deriv (fun s => (γ s).2) t = speed γ t * Real.sin (α t)

def FieldBound (P Q : Point → ℝ) (γ : ℝ → Point) (M : ℝ) : Prop :=
  ∀ t, t ∈ Set.Icc (0 : ℝ) 1 →
    Real.sqrt (P (γ t) ^ 2 + Q (γ t) ^ 2) ≤ M

def AdmissibleData (P Q : Point → ℝ) (γ : ℝ → Point) : Prop :=
  Continuous P ∧ Continuous Q ∧ ContDiff ℝ 1 γ

private theorem speed_nonnegative (γ : ℝ → Point) (t : ℝ) :
    0 ≤ speed γ t := by
  unfold speed
  exact Real.sqrt_nonneg _

private theorem abs_dot_product_le_euclidean (a b x y : ℝ) :
    |a * x + b * y| ≤
      Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (x ^ 2 + y ^ 2) := by
  have hab : 0 ≤ a ^ 2 + b ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hxy : 0 ≤ x ^ 2 + y ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsqrt_ab := Real.sq_sqrt hab
  have hsqrt_xy := Real.sq_sqrt hxy
  have hidentity :
      (a * x + b * y) ^ 2 + (a * y - b * x) ^ 2 =
        (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by
    ring
  have hsq :
      (a * x + b * y) ^ 2 ≤
        (Real.sqrt (a ^ 2 + b ^ 2) *
          Real.sqrt (x ^ 2 + y ^ 2)) ^ 2 := by
    rw [mul_pow, hsqrt_ab, hsqrt_xy]
    nlinarith [sq_nonneg (a * y - b * x)]
  have hnonneg :
      0 ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (x ^ 2 + y ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [abs_le]
  constructor <;> nlinarith

private theorem continuous_deriv_clm_comp_of_contDiff_one
    (L : Point →L[ℝ] ℝ) {γ : ℝ → Point}
    (hγ : ContDiff ℝ 1 γ) :
    Continuous (fun t : ℝ => deriv (fun s : ℝ => L (γ s)) t) := by
  have hdiff : Differentiable ℝ γ :=
    (contDiff_one_iff_fderiv.mp hγ).1
  have hfd : Continuous (fun t : ℝ => fderiv ℝ γ t) :=
    (contDiff_one_iff_fderiv.mp hγ).2
  have heval :
      Continuous (fun t : ℝ => (fderiv ℝ γ t) (1 : ℝ)) :=
    hfd.clm_apply
      (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
  have hout :
      Continuous (fun t : ℝ => L ((fderiv ℝ γ t) (1 : ℝ))) := by
    simpa [Function.comp_def] using L.continuous.comp heval
  have heq :
      (fun t : ℝ => deriv (fun s : ℝ => L (γ s)) t) =
        (fun t : ℝ => L ((fderiv ℝ γ t) (1 : ℝ))) := by
    funext t
    have hcomp :
        HasFDerivAt (fun s : ℝ => L (γ s))
          (L.comp (fderiv ℝ γ t)) t := by
      simpa [Function.comp_def] using
        ((L.hasFDerivAt :
            HasFDerivAt (fun p : Point => L p) L (γ t)).comp
          t (hdiff t).hasFDerivAt)
    change
      (fderiv ℝ (fun s : ℝ => L (γ s)) t) (1 : ℝ) =
        L ((fderiv ℝ γ t) (1 : ℝ))
    rw [hcomp.fderiv]
    rfl
  rw [heq]
  exact hout

theorem gap1 (P Q : Point → ℝ) (γ : ℝ → Point) (α : ℝ → ℝ)
    (hα : HasTangentAngle γ α) :
    |lineIntegral P Q γ| = |projectedIntegral P Q γ α| := by
  apply congrArg abs
  unfold lineIntegral projectedIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
  rcases hα t ht' with ⟨hx, hy⟩
  change
    P (γ t) * deriv (fun s => (γ s).1) t +
        Q (γ t) * deriv (fun s => (γ s).2) t =
      (P (γ t) * Real.cos (α t) + Q (γ t) * Real.sin (α t)) *
        speed γ t
  rw [hx, hy]
  ring

theorem gap2 (P Q : Point → ℝ) (γ : ℝ → Point) (α : ℝ → ℝ)
    (hdata : AdmissibleData P Q γ) :
    |projectedIntegral P Q γ α| ≤
      absoluteProjectedIntegral P Q γ α := by
  unfold projectedIntegral absoluteProjectedIntegral
  calc
    |∫ t in (0 : ℝ)..1,
        (P (γ t) * Real.cos (α t) + Q (γ t) * Real.sin (α t)) *
          speed γ t| ≤
        ∫ t in (0 : ℝ)..1,
          |(P (γ t) * Real.cos (α t) + Q (γ t) * Real.sin (α t)) *
            speed γ t| :=
      intervalIntegral.abs_integral_le_integral_abs
        (zero_le_one : (0 : ℝ) ≤ 1)
    _ = ∫ t in (0 : ℝ)..1,
          |P (γ t) * Real.cos (α t) + Q (γ t) * Real.sin (α t)| *
            speed γ t := by
      apply intervalIntegral.integral_congr
      intro t _
      change
        |(P (γ t) * Real.cos (α t) + Q (γ t) * Real.sin (α t)) *
            speed γ t| =
          |P (γ t) * Real.cos (α t) + Q (γ t) * Real.sin (α t)| *
            speed γ t
      rw [abs_mul, abs_of_nonneg (speed_nonnegative γ t)]

theorem gap3 (P Q : Point → ℝ) (γ : ℝ → Point) (α : ℝ → ℝ)
    (hdata : AdmissibleData P Q γ) (hα : HasTangentAngle γ α) :
    |lineIntegral P Q γ| ≤ absoluteProjectedIntegral P Q γ α := by
  calc
    |lineIntegral P Q γ| = |projectedIntegral P Q γ α| :=
      gap1 P Q γ α hα
    _ ≤ absoluteProjectedIntegral P Q γ α :=
      gap2 P Q γ α hdata

theorem gap4 (P Q : Point → ℝ) (p : Point) (α : ℝ) :
    (P p * Real.cos α + Q p * Real.sin α) ^ 2 +
        (P p * Real.sin α - Q p * Real.cos α) ^ 2 =
      P p ^ 2 + Q p ^ 2 := by
  calc
    (P p * Real.cos α + Q p * Real.sin α) ^ 2 +
        (P p * Real.sin α - Q p * Real.cos α) ^ 2 =
      (P p ^ 2 + Q p ^ 2) *
        (Real.sin α ^ 2 + Real.cos α ^ 2) := by
          ring
    _ = P p ^ 2 + Q p ^ 2 := by
      rw [Real.sin_sq_add_cos_sq]
      ring

theorem gap5 (P Q : Point → ℝ) (p : Point) (α : ℝ) :
    (P p * Real.cos α + Q p * Real.sin α) ^ 2 ≤
      P p ^ 2 + Q p ^ 2 := by
  have hidentity := gap4 P Q p α
  have hnonneg :
      0 ≤ (P p * Real.sin α - Q p * Real.cos α) ^ 2 :=
    sq_nonneg _
  nlinarith

theorem gap6 (P Q : Point → ℝ) (p : Point) (α : ℝ) :
    |P p * Real.cos α + Q p * Real.sin α| ≤
      Real.sqrt (P p ^ 2 + Q p ^ 2) := by
  have hsq := gap5 P Q p α
  have hsum : 0 ≤ P p ^ 2 + Q p ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsqrt_sq := Real.sq_sqrt hsum
  have hsqrt_nonneg := Real.sqrt_nonneg (P p ^ 2 + Q p ^ 2)
  rw [abs_le]
  constructor <;> nlinarith

theorem gap7 (P Q : Point → ℝ) (γ : ℝ → Point) (M : ℝ)
    (hM : FieldBound P Q γ M) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt (P (γ t) ^ 2 + Q (γ t) ^ 2) ≤ M := by
  exact hM t ht

theorem gap8 (P Q : Point → ℝ) (γ : ℝ → Point) (α : ℝ → ℝ) (M : ℝ)
    (hM : FieldBound P Q γ M) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |P (γ t) * Real.cos (α t) + Q (γ t) * Real.sin (α t)| ≤ M := by
  exact le_trans (gap6 P Q (γ t) (α t)) (hM t ht)

theorem gap9 (P Q : Point → ℝ) (γ : ℝ → Point) (M : ℝ)
    (hdata : AdmissibleData P Q γ) (hM : FieldBound P Q γ M) :
    |lineIntegral P Q γ| ≤ M * arcLength γ := by
  unfold lineIntegral
  rcases hdata with ⟨hP, hQ, hγ⟩
  have hγcont : Continuous γ := hγ.continuous
  have hdx : Continuous (fun t => deriv (fun s => (γ s).1) t) := by
    simpa using
      (continuous_deriv_clm_comp_of_contDiff_one
        (ContinuousLinearMap.fst ℝ ℝ ℝ) hγ)
  have hdy : Continuous (fun t => deriv (fun s => (γ s).2) t) := by
    simpa using
      (continuous_deriv_clm_comp_of_contDiff_one
        (ContinuousLinearMap.snd ℝ ℝ ℝ) hγ)
  have hPγ : Continuous (fun t => P (γ t)) := hP.comp hγcont
  have hQγ : Continuous (fun t => Q (γ t)) := hQ.comp hγcont
  have hline :
      Continuous (fun t : ℝ =>
        P (γ t) * deriv (fun s => (γ s).1) t +
          Q (γ t) * deriv (fun s => (γ s).2) t) :=
    (hPγ.mul hdx).add (hQγ.mul hdy)
  have hspeed : Continuous (fun t : ℝ => speed γ t) := by
    unfold speed
    exact Real.continuous_sqrt.comp ((hdx.pow 2).add (hdy.pow 2))
  have habsInt :
      IntervalIntegrable
        (fun t : ℝ =>
          |P (γ t) * deriv (fun s => (γ s).1) t +
            Q (γ t) * deriv (fun s => (γ s).2) t|)
        MeasureTheory.volume 0 1 :=
    hline.abs.intervalIntegrable (0 : ℝ) 1
  have hbound : Continuous (fun t : ℝ => M * speed γ t) :=
    (continuous_const : Continuous (fun _ : ℝ => M)).mul hspeed
  have hboundInt :
      IntervalIntegrable (fun t : ℝ => M * speed γ t)
        MeasureTheory.volume 0 1 :=
    hbound.intervalIntegrable (0 : ℝ) 1
  have hpoint :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |P (γ t) * deriv (fun s => (γ s).1) t +
          Q (γ t) * deriv (fun s => (γ s).2) t| ≤ M * speed γ t := by
    intro t ht
    calc
      |P (γ t) * deriv (fun s => (γ s).1) t +
          Q (γ t) * deriv (fun s => (γ s).2) t| ≤
        Real.sqrt (P (γ t) ^ 2 + Q (γ t) ^ 2) *
          Real.sqrt
            (deriv (fun s => (γ s).1) t ^ 2 +
              deriv (fun s => (γ s).2) t ^ 2) :=
        abs_dot_product_le_euclidean
          (P (γ t)) (Q (γ t))
          (deriv (fun s => (γ s).1) t)
          (deriv (fun s => (γ s).2) t)
      _ ≤ M *
          Real.sqrt
            (deriv (fun s => (γ s).1) t ^ 2 +
              deriv (fun s => (γ s).2) t ^ 2) :=
        mul_le_mul_of_nonneg_right (hM t ht) (Real.sqrt_nonneg _)
      _ = M * speed γ t := by
        rfl
  calc
    |∫ t in (0 : ℝ)..1,
        P (γ t) * deriv (fun s => (γ s).1) t +
          Q (γ t) * deriv (fun s => (γ s).2) t| ≤
      ∫ t in (0 : ℝ)..1,
        |P (γ t) * deriv (fun s => (γ s).1) t +
          Q (γ t) * deriv (fun s => (γ s).2) t| :=
      intervalIntegral.abs_integral_le_integral_abs
        (zero_le_one : (0 : ℝ) ≤ 1)
    _ ≤ ∫ t in (0 : ℝ)..1, M * speed γ t :=
      intervalIntegral.integral_mono_on
        (zero_le_one : (0 : ℝ) ≤ 1) habsInt hboundInt hpoint
    _ = M * arcLength γ := by
      simp [arcLength]

theorem gap10 (γ : ℝ → Point) (M : ℝ) :
    M * arcLength γ = arcLength γ * M := by
  exact mul_comm M (arcLength γ)

theorem gap11 (P Q : Point → ℝ) (γ : ℝ → Point) (M : ℝ)
    (hdata : AdmissibleData P Q γ) (hM : FieldBound P Q γ M) :
    |lineIntegral P Q γ| ≤ arcLength γ * M := by
  calc
    |lineIntegral P Q γ| ≤ M * arcLength γ :=
      gap9 P Q γ M hdata hM
    _ = arcLength γ * M := mul_comm _ _

theorem gap12 (P Q : Point → ℝ) (γ : ℝ → Point) (M : ℝ)
    (hdata : AdmissibleData P Q γ) (hM : FieldBound P Q γ M) :
    |lineIntegral P Q γ| ≤ arcLength γ * M := by
  exact gap11 P Q γ M hdata hM

end

end ProofGap.Exercise4277
