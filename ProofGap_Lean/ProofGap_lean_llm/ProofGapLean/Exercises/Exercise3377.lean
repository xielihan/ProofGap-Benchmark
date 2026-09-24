import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3377

noncomputable section

def curveEquation (x y : ℝ) : Prop :=
  x ^ 2 * y ^ 2 + x ^ 2 + y ^ 2 - 1 = 0

def IsPositiveProductCurveParam (D : Set ℝ)
    (x y : ℝ → ℝ) : Prop :=
  IsOpen D ∧ DifferentiableOn ℝ x D ∧
    DifferentiableOn ℝ y D ∧
      ∀ t ∈ D, curveEquation (x t) (y t) ∧ 0 < x t * y t

theorem gap1 (D : Set ℝ) (x y : ℝ → ℝ)
    (h : IsPositiveProductCurveParam D x y) :
    ∀ t ∈ D,
      2 * x t * (y t) ^ 2 * deriv x t +
        2 * (x t) ^ 2 * y t * deriv y t +
        2 * x t * deriv x t + 2 * y t * deriv y t = 0 := by
  intro t ht
  rcases h with ⟨hD, hxD, hyD, hcurve⟩
  have hxt : DifferentiableAt ℝ x t :=
    (hxD t ht).differentiableAt (hD.mem_nhds ht)
  have hyt : DifferentiableAt ℝ y t :=
    (hyD t ht).differentiableAt (hD.mem_nhds ht)
  have hx' : HasDerivAt x (deriv x t) t := hxt.hasDerivAt
  have hy' : HasDerivAt y (deriv y t) t := hyt.hasDerivAt
  have hx2 : HasDerivAt (fun s : ℝ => x s ^ 2)
      (2 * x t * deriv x t) t := by
    convert hx'.mul hx' using 1
    · funext s
      simp [pow_two]
    · ring
  have hy2 : HasDerivAt (fun s : ℝ => y s ^ 2)
      (2 * y t * deriv y t) t := by
    convert hy'.mul hy' using 1
    · funext s
      simp [pow_two]
    · ring
  have hF : HasDerivAt
      (fun s : ℝ => x s ^ 2 * y s ^ 2 + x s ^ 2 + y s ^ 2 - 1)
      (2 * x t * (y t) ^ 2 * deriv x t +
        2 * (x t) ^ 2 * y t * deriv y t +
        2 * x t * deriv x t + 2 * y t * deriv y t) t := by
    convert ((((hx2.mul hy2).add hx2).add hy2).sub_const 1) using 1 <;> ring
  have heq :
      (fun s : ℝ => x s ^ 2 * y s ^ 2 + x s ^ 2 + y s ^ 2 - 1) =ᶠ[nhds t]
        (fun _ : ℝ => 0) := by
    filter_upwards [hD.mem_nhds ht] with s hs
    simpa [curveEquation] using (hcurve s hs).1
  calc
    2 * x t * (y t) ^ 2 * deriv x t +
          2 * (x t) ^ 2 * y t * deriv y t +
          2 * x t * deriv x t + 2 * y t * deriv y t =
        deriv (fun s : ℝ => x s ^ 2 * y s ^ 2 + x s ^ 2 + y s ^ 2 - 1) t :=
      hF.deriv.symm
    _ = deriv (fun _ : ℝ => 0) t := heq.deriv_eq
    _ = 0 := by simp

theorem gap2 (D : Set ℝ) (x y : ℝ → ℝ)
    (h : IsPositiveProductCurveParam D x y) :
    ∀ t ∈ D,
      x t * ((y t) ^ 2 + 1) * deriv x t +
        y t * ((x t) ^ 2 + 1) * deriv y t = 0 := by
  intro t ht
  have h1 := gap1 D x y h t ht
  calc
    x t * ((y t) ^ 2 + 1) * deriv x t +
          y t * ((x t) ^ 2 + 1) * deriv y t =
        (1 / 2 : ℝ) *
          (2 * x t * (y t) ^ 2 * deriv x t +
            2 * (x t) ^ 2 * y t * deriv y t +
            2 * x t * deriv x t + 2 * y t * deriv y t) := by ring
    _ = 0 := by rw [h1]; norm_num

theorem gap3 (D : Set ℝ) (x y : ℝ → ℝ)
    (h : IsPositiveProductCurveParam D x y) :
    ∀ t ∈ D,
      x t = Real.sqrt ((1 - (y t) ^ 2) / (1 + (y t) ^ 2)) ∨
        x t = -Real.sqrt ((1 - (y t) ^ 2) / (1 + (y t) ^ 2)) := by
  intro t ht
  have hc := (h.2.2.2 t ht).1
  simp only [curveEquation] at hc
  have hden : 0 < 1 + (y t) ^ 2 := by positivity
  have hratio :
      (1 - (y t) ^ 2) / (1 + (y t) ^ 2) = (x t) ^ 2 := by
    apply (div_eq_iff (ne_of_gt hden)).2
    nlinarith [hc]
  rw [hratio, Real.sqrt_sq_eq_abs]
  rcases le_total 0 (x t) with hx | hx
  · exact Or.inl (abs_of_nonneg hx).symm
  · exact Or.inr (by rw [abs_of_nonpos hx]; ring)

theorem gap4 (D : Set ℝ) (x y : ℝ → ℝ)
    (h : IsPositiveProductCurveParam D x y) :
    ∀ t ∈ D,
      y t = Real.sqrt ((1 - (x t) ^ 2) / (1 + (x t) ^ 2)) ∨
        y t = -Real.sqrt ((1 - (x t) ^ 2) / (1 + (x t) ^ 2)) := by
  intro t ht
  have hc := (h.2.2.2 t ht).1
  simp only [curveEquation] at hc
  have hden : 0 < 1 + (x t) ^ 2 := by positivity
  have hratio :
      (1 - (x t) ^ 2) / (1 + (x t) ^ 2) = (y t) ^ 2 := by
    apply (div_eq_iff (ne_of_gt hden)).2
    nlinarith [hc]
  rw [hratio, Real.sqrt_sq_eq_abs]
  rcases le_total 0 (y t) with hy | hy
  · exact Or.inl (abs_of_nonneg hy).symm
  · exact Or.inr (by rw [abs_of_nonpos hy]; ring)

theorem gap5 (D : Set ℝ) (x y : ℝ → ℝ)
    (h : IsPositiveProductCurveParam D x y) :
    ∀ t ∈ D,
      (0 < x t ∧ 0 < y t) ∨ (x t < 0 ∧ y t < 0) := by
  intro t ht
  exact (mul_pos_iff.mp (h.2.2.2 t ht).2)

theorem gap6 (D : Set ℝ) (x y : ℝ → ℝ)
    (h : IsPositiveProductCurveParam D x y) :
    ∀ t ∈ D,
      deriv x t / Real.sqrt (1 - (x t) ^ 4) +
        deriv y t / Real.sqrt (1 - (y t) ^ 4) = 0 := by
  intro t ht
  have hc := (h.2.2.2 t ht).1
  simp only [curveEquation] at hc
  have hbaseX :
      1 - (x t) ^ 2 = (y t) ^ 2 * (1 + (x t) ^ 2) := by
    nlinarith [hc]
  have hbaseY :
      1 - (y t) ^ 2 = (x t) ^ 2 * (1 + (y t) ^ 2) := by
    nlinarith [hc]
  have hidX :
      1 - (x t) ^ 4 = (y t) ^ 2 * (1 + (x t) ^ 2) ^ 2 := by
    calc
      1 - (x t) ^ 4 =
          (1 - (x t) ^ 2) * (1 + (x t) ^ 2) := by ring
      _ = ((y t) ^ 2 * (1 + (x t) ^ 2)) *
          (1 + (x t) ^ 2) := by rw [hbaseX]
      _ = (y t) ^ 2 * (1 + (x t) ^ 2) ^ 2 := by ring
  have hidY :
      1 - (y t) ^ 4 = (x t) ^ 2 * (1 + (y t) ^ 2) ^ 2 := by
    calc
      1 - (y t) ^ 4 =
          (1 - (y t) ^ 2) * (1 + (y t) ^ 2) := by ring
      _ = ((x t) ^ 2 * (1 + (y t) ^ 2)) *
          (1 + (y t) ^ 2) := by rw [hbaseY]
      _ = (x t) ^ 2 * (1 + (y t) ^ 2) ^ 2 := by ring
  have hsquareX :
      (|y t| * (1 + (x t) ^ 2)) ^ 2 = 1 - (x t) ^ 4 := by
    calc
      (|y t| * (1 + (x t) ^ 2)) ^ 2 =
          |y t| ^ 2 * (1 + (x t) ^ 2) ^ 2 := by ring
      _ = (y t) ^ 2 * (1 + (x t) ^ 2) ^ 2 := by rw [sq_abs]
      _ = 1 - (x t) ^ 4 := hidX.symm
  have hsquareY :
      (|x t| * (1 + (y t) ^ 2)) ^ 2 = 1 - (y t) ^ 4 := by
    calc
      (|x t| * (1 + (y t) ^ 2)) ^ 2 =
          |x t| ^ 2 * (1 + (y t) ^ 2) ^ 2 := by ring
      _ = (x t) ^ 2 * (1 + (y t) ^ 2) ^ 2 := by rw [sq_abs]
      _ = 1 - (y t) ^ 4 := hidY.symm
  have hsqrtX :
      Real.sqrt (1 - (x t) ^ 4) = |y t| * (1 + (x t) ^ 2) := by
    rw [← hsquareX]
    exact Real.sqrt_sq (mul_nonneg (abs_nonneg _) (by positivity))
  have hsqrtY :
      Real.sqrt (1 - (y t) ^ 4) = |x t| * (1 + (y t) ^ 2) := by
    rw [← hsquareY]
    exact Real.sqrt_sq (mul_nonneg (abs_nonneg _) (by positivity))
  have hrel := gap2 D x y h t ht
  rcases gap5 D x y h t ht with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hx0 : x t ≠ 0 := ne_of_gt hx
    have hy0 : y t ≠ 0 := ne_of_gt hy
    have hdx0 : 1 + (x t) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    have hdy0 : 1 + (y t) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    rw [hsqrtX, hsqrtY, abs_of_pos hy, abs_of_pos hx]
    field_simp [hx0, hy0, hdx0, hdy0]
    ring_nf at hrel ⊢
    linarith
  · have hx0 : x t ≠ 0 := ne_of_lt hx
    have hy0 : y t ≠ 0 := ne_of_lt hy
    have hdx0 : 1 + (x t) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    have hdy0 : 1 + (y t) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    rw [hsqrtX, hsqrtY, abs_of_neg hy, abs_of_neg hx]
    field_simp [hx0, hy0, hdx0, hdy0]
    ring_nf at hrel ⊢
    linarith

theorem gap7 (D : Set ℝ) (x y : ℝ → ℝ)
    (h : IsPositiveProductCurveParam D x y) :
    ∀ t ∈ D,
      deriv x t / Real.sqrt (1 - (x t) ^ 4) +
        deriv y t / Real.sqrt (1 - (y t) ^ 4) = 0 := by
  exact gap6 D x y h

end

end ProofGap.Exercise3377
