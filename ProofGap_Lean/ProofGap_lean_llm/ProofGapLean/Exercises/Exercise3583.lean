import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3583

noncomputable section

structure Point2 where
  x : ℝ
  y : ℝ

def polynomial (p : Point2) : ℝ :=
  p.x ^ 2 * p.y + p.x * p.y ^ 2 - 2 * p.x * p.y

def partialX (f : Point2 → ℝ) (p : Point2) : ℝ :=
  deriv (fun t => f ⟨t, p.y⟩) p.x

def partialY (f : Point2 → ℝ) (p : Point2) : ℝ :=
  deriv (fun t => f ⟨p.x, t⟩) p.y

def partialXX (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialX (partialX f) p

def partialXY (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialY (partialX f) p

def partialYY (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialY (partialY f) p

def partialXXX (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialX (partialXX f) p

def partialXXY (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialY (partialXX f) p

def partialXYY (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialY (partialXY f) p

def partialYYY (f : Point2 → ℝ) (p : Point2) : ℝ :=
  partialY (partialYY f) p

def basePoint : Point2 := ⟨1, -1⟩

def shiftedPoint (h k : ℝ) : Point2 := ⟨1 + h, -1 + k⟩

def increment (h k : ℝ) : ℝ :=
  polynomial (shiftedPoint h k) - polynomial basePoint

def taylorIncrement3 (h k : ℝ) : ℝ :=
  h - 3 * k - h ^ 2 - 2 * h * k + k ^ 2 + h * k * (h + k)

def remainder3 (h k : ℝ) : ℝ :=
  increment h k - taylorIncrement3 h k

private theorem deriv_quadratic_aux (a b c x : ℝ) :
    deriv (fun t : ℝ => a * t ^ 2 + b * t + c) x =
      2 * a * x + b := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have hsq :
      HasDerivAt (fun t : ℝ => t * t) (1 * x + x * 1) x :=
    hid.mul hid
  have hpoly :
      HasDerivAt
        (fun t : ℝ => a * (t * t) + b * t + c)
        (a * (1 * x + x * 1) + b * 1) x :=
    ((hsq.const_mul a).add (hid.const_mul b)).add_const c
  have hpoly' :
      HasDerivAt
        (fun t : ℝ => a * t ^ 2 + b * t + c)
        (a * (1 * x + x * 1) + b * 1) x := by
    simpa only [pow_two] using hpoly
  rw [hpoly'.deriv]
  ring

theorem gap1 :
    ∀ p : Point2,
      partialX polynomial p = 2 * p.x * p.y + p.y ^ 2 - 2 * p.y := by
  intro p
  unfold partialX
  have hf :
      (fun t : ℝ => polynomial ⟨t, p.y⟩) =
        (fun t : ℝ =>
          p.y * t ^ 2 + (p.y ^ 2 - 2 * p.y) * t + 0) := by
    funext t
    simp [polynomial]
    ring
  rw [hf, deriv_quadratic_aux]
  ring

theorem gap2 :
    partialX polynomial basePoint = 1 := by
  rw [gap1]
  norm_num [basePoint]

theorem gap3 :
    ∀ p : Point2,
      partialY polynomial p = p.x ^ 2 + 2 * p.x * p.y - 2 * p.x := by
  intro p
  unfold partialY
  have hf :
      (fun t : ℝ => polynomial ⟨p.x, t⟩) =
        (fun t : ℝ =>
          p.x * t ^ 2 + (p.x ^ 2 - 2 * p.x) * t + 0) := by
    funext t
    simp [polynomial]
    ring
  rw [hf, deriv_quadratic_aux]
  ring

theorem gap4 :
    partialY polynomial basePoint = -3 := by
  rw [gap3]
  norm_num [basePoint]

theorem gap5 :
    ∀ p : Point2, partialXX polynomial p = 2 * p.y := by
  intro p
  change deriv (fun t : ℝ => partialX polynomial ⟨t, p.y⟩) p.x = 2 * p.y
  have hf :
      (fun t : ℝ => partialX polynomial ⟨t, p.y⟩) =
        (fun t : ℝ =>
          0 * t ^ 2 + (2 * p.y) * t + (p.y ^ 2 - 2 * p.y)) := by
    funext t
    rw [gap1]
    ring
  rw [hf, deriv_quadratic_aux]
  ring

theorem gap6 :
    partialXX polynomial basePoint = -2 := by
  rw [gap5]
  norm_num [basePoint]

theorem gap7 :
    ∀ p : Point2, partialYY polynomial p = 2 * p.x := by
  intro p
  change deriv (fun t : ℝ => partialY polynomial ⟨p.x, t⟩) p.y = 2 * p.x
  have hf :
      (fun t : ℝ => partialY polynomial ⟨p.x, t⟩) =
        (fun t : ℝ =>
          0 * t ^ 2 + (2 * p.x) * t + (p.x ^ 2 - 2 * p.x)) := by
    funext t
    rw [gap3]
    ring
  rw [hf, deriv_quadratic_aux]
  ring

theorem gap8 :
    partialYY polynomial basePoint = 2 := by
  rw [gap7]
  norm_num [basePoint]

theorem gap9 :
    ∀ p : Point2,
      partialXY polynomial p = 2 * p.x + 2 * p.y - 2 := by
  intro p
  rw [partialXY]
  unfold partialY
  have hf :
      (fun t : ℝ => partialX polynomial ⟨p.x, t⟩) =
        (fun t : ℝ =>
          1 * t ^ 2 + (2 * p.x - 2) * t + 0) := by
    funext t
    rw [gap1]
    ring
  rw [hf, deriv_quadratic_aux]
  ring

theorem gap10 :
    partialXY polynomial basePoint = -2 := by
  rw [gap9]
  norm_num [basePoint]

theorem gap11 :
    partialXXX polynomial basePoint = partialYYY polynomial basePoint := by
  have hxxx : partialXXX polynomial basePoint = 0 := by
    change
      deriv (fun t : ℝ => partialXX polynomial ⟨t, basePoint.y⟩)
        basePoint.x = 0
    have hf :
        (fun t : ℝ => partialXX polynomial ⟨t, basePoint.y⟩) =
          (fun t : ℝ => 0 * t ^ 2 + 0 * t + 2 * basePoint.y) := by
      funext t
      rw [gap5]
      simp
    rw [hf, deriv_quadratic_aux]
    ring
  have hyyy : partialYYY polynomial basePoint = 0 := by
    change
      deriv (fun t : ℝ => partialYY polynomial ⟨basePoint.x, t⟩)
        basePoint.y = 0
    have hf :
        (fun t : ℝ => partialYY polynomial ⟨basePoint.x, t⟩) =
          (fun t : ℝ => 0 * t ^ 2 + 0 * t + 2 * basePoint.x) := by
      funext t
      rw [gap7]
      simp
    rw [hf, deriv_quadratic_aux]
    ring
  rw [hxxx, hyyy]

theorem gap12 :
    partialYYY polynomial basePoint = 0 := by
  change
    deriv (fun t : ℝ => partialYY polynomial ⟨basePoint.x, t⟩)
      basePoint.y = 0
  have hf :
      (fun t : ℝ => partialYY polynomial ⟨basePoint.x, t⟩) =
        (fun t : ℝ => 0 * t ^ 2 + 0 * t + 2 * basePoint.x) := by
    funext t
    rw [gap7]
    simp
  rw [hf, deriv_quadratic_aux]
  ring

theorem gap13 :
    partialXXY polynomial basePoint = partialXYY polynomial basePoint := by
  have hxxy : partialXXY polynomial basePoint = 2 := by
    change
      deriv (fun t : ℝ => partialXX polynomial ⟨basePoint.x, t⟩)
        basePoint.y = 2
    have hf :
        (fun t : ℝ => partialXX polynomial ⟨basePoint.x, t⟩) =
          (fun t : ℝ => 0 * t ^ 2 + 2 * t + 0) := by
      funext t
      rw [gap5]
      simp
    rw [hf, deriv_quadratic_aux]
    ring
  have hxyy : partialXYY polynomial basePoint = 2 := by
    change
      deriv (fun t : ℝ => partialXY polynomial ⟨basePoint.x, t⟩)
        basePoint.y = 2
    have hf :
        (fun t : ℝ => partialXY polynomial ⟨basePoint.x, t⟩) =
          (fun t : ℝ =>
            0 * t ^ 2 + 2 * t + (2 * basePoint.x - 2)) := by
      funext t
      rw [gap9]
      ring
    rw [hf, deriv_quadratic_aux]
    ring
  rw [hxxy, hxyy]

theorem gap14 :
    partialXYY polynomial basePoint = 2 := by
  rw [partialXYY]
  unfold partialY
  have hf :
      (fun t : ℝ => partialXY polynomial ⟨basePoint.x, t⟩) =
        (fun t : ℝ =>
          0 * t ^ 2 + 2 * t + (2 * basePoint.x - 2)) := by
    funext t
    rw [gap9]
    ring
  rw [hf, deriv_quadratic_aux]
  ring

theorem gap15 :
    ∀ h k : ℝ, remainder3 h k = 0 := by
  intro h k
  unfold remainder3 increment taylorIncrement3 shiftedPoint basePoint polynomial
  ring

theorem gap16 :
    ∀ h k : ℝ,
      increment h k =
        polynomial (shiftedPoint h k) - polynomial basePoint := by
  intro h k
  rfl

theorem gap17 :
    ∀ h k : ℝ, increment h k = taylorIncrement3 h k := by
  intro h k
  have hr := gap15 h k
  unfold remainder3 at hr
  exact sub_eq_zero.mp hr

theorem gap18 :
    ∀ h k : ℝ,
      taylorIncrement3 h k =
        h - 3 * k - h ^ 2 - 2 * h * k + k ^ 2 +
          h * k * (h + k) := by
  intro h k
  rfl

theorem gap19 :
    ∀ h k : ℝ,
      increment h k =
        h - 3 * k - h ^ 2 - 2 * h * k + k ^ 2 +
          h * k * (h + k) := by
  intro h k
  calc
    increment h k = taylorIncrement3 h k := gap17 h k
    _ = h - 3 * k - h ^ 2 - 2 * h * k + k ^ 2 +
          h * k * (h + k) := gap18 h k

end

end ProofGap.Exercise3583
