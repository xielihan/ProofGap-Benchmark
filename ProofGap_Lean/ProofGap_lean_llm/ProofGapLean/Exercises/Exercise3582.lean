import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3582

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def polynomial (p : Point3) : ℝ :=
  p.x ^ 3 + p.y ^ 3 + p.z ^ 3 - 3 * p.x * p.y * p.z

def partialX (f : Point3 → ℝ) (p : Point3) : ℝ :=
  deriv (fun t => f ⟨t, p.y, p.z⟩) p.x

def partialY (f : Point3 → ℝ) (p : Point3) : ℝ :=
  deriv (fun t => f ⟨p.x, t, p.z⟩) p.y

def partialZ (f : Point3 → ℝ) (p : Point3) : ℝ :=
  deriv (fun t => f ⟨p.x, p.y, t⟩) p.z

def partialXX (f : Point3 → ℝ) (p : Point3) : ℝ :=
  partialX (partialX f) p

def partialYY (f : Point3 → ℝ) (p : Point3) : ℝ :=
  partialY (partialY f) p

def partialZZ (f : Point3 → ℝ) (p : Point3) : ℝ :=
  partialZ (partialZ f) p

def partialXY (f : Point3 → ℝ) (p : Point3) : ℝ :=
  partialY (partialX f) p

def partialYZ (f : Point3 → ℝ) (p : Point3) : ℝ :=
  partialZ (partialY f) p

def partialXZ (f : Point3 → ℝ) (p : Point3) : ℝ :=
  partialZ (partialX f) p

def partialXXX (f : Point3 → ℝ) (p : Point3) : ℝ :=
  partialX (partialXX f) p

def partialYYY (f : Point3 → ℝ) (p : Point3) : ℝ :=
  partialY (partialYY f) p

def partialZZZ (f : Point3 → ℝ) (p : Point3) : ℝ :=
  partialZ (partialZZ f) p

def partialXYZ (f : Point3 → ℝ) (p : Point3) : ℝ :=
  partialZ (partialXY f) p

def basePoint : Point3 := ⟨1, 1, 1⟩

def taylorPolynomial3 (p : Point3) : ℝ :=
  3 * ((p.x - 1) ^ 2 + (p.y - 1) ^ 2 + (p.z - 1) ^ 2 -
      (p.x - 1) * (p.y - 1) - (p.x - 1) * (p.z - 1) -
      (p.y - 1) * (p.z - 1)) +
    (p.x - 1) ^ 3 + (p.y - 1) ^ 3 + (p.z - 1) ^ 3 -
    3 * (p.x - 1) * (p.y - 1) * (p.z - 1)

def remainder3 (p : Point3) : ℝ :=
  polynomial p - taylorPolynomial3 p

private theorem deriv_cubic_polynomial (a b c d x : ℝ) :
    deriv (fun t : ℝ => a * t ^ 3 + b * t ^ 2 + c * t + d) x =
      3 * a * x ^ 2 + 2 * b * x + c := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have hsquare : HasDerivAt (fun t : ℝ => t * t) (2 * x) x := by
    convert hid.mul hid using 1 <;> ring
  have hcube : HasDerivAt (fun t : ℝ => (t * t) * t) (3 * x ^ 2) x := by
    convert hsquare.mul hid using 1 <;> ring
  have ha : HasDerivAt (fun t : ℝ => a * ((t * t) * t)) (3 * a * x ^ 2) x := by
    convert (hasDerivAt_const x a).mul hcube using 1 <;> ring
  have hb : HasDerivAt (fun t : ℝ => b * (t * t)) (2 * b * x) x := by
    convert (hasDerivAt_const x b).mul hsquare using 1 <;> ring
  have hc : HasDerivAt (fun t : ℝ => c * t) c x := by
    convert (hasDerivAt_const x c).mul hid using 1 <;> ring
  have hd : HasDerivAt (fun _ : ℝ => d) 0 x := hasDerivAt_const x d
  have hsum : HasDerivAt
      (fun t : ℝ => a * ((t * t) * t) + b * (t * t) + c * t + d)
      (((3 * a * x ^ 2 + 2 * b * x) + c) + 0) x :=
    ((ha.add hb).add hc).add hd
  calc
    deriv (fun t : ℝ => a * t ^ 3 + b * t ^ 2 + c * t + d) x =
        deriv (fun t : ℝ => a * ((t * t) * t) + b * (t * t) + c * t + d) x := by
      apply congrArg (fun f : ℝ → ℝ => deriv f x)
      funext t
      ring
    _ = ((3 * a * x ^ 2 + 2 * b * x) + c) + 0 := hsum.deriv
    _ = 3 * a * x ^ 2 + 2 * b * x + c := by ring

theorem gap1 :
    ∀ p : Point3,
      partialX polynomial p = 3 * p.x ^ 2 - 3 * p.y * p.z := by
  intro p
  simp only [partialX, polynomial]
  calc
    deriv (fun t : ℝ => t ^ 3 + p.y ^ 3 + p.z ^ 3 - 3 * t * p.y * p.z) p.x =
        deriv (fun t : ℝ => 1 * t ^ 3 + 0 * t ^ 2 + (-3 * p.y * p.z) * t +
          (p.y ^ 3 + p.z ^ 3)) p.x := by
      apply congrArg (fun f : ℝ → ℝ => deriv f p.x)
      funext t
      ring
    _ = 3 * 1 * p.x ^ 2 + 2 * 0 * p.x + (-3 * p.y * p.z) :=
      deriv_cubic_polynomial 1 0 (-3 * p.y * p.z) (p.y ^ 3 + p.z ^ 3) p.x
    _ = 3 * p.x ^ 2 - 3 * p.y * p.z := by ring

theorem gap2 :
    ∀ p : Point3,
      partialY polynomial p = 3 * p.y ^ 2 - 3 * p.x * p.z := by
  intro p
  simp only [partialY, polynomial]
  calc
    deriv (fun t : ℝ => p.x ^ 3 + t ^ 3 + p.z ^ 3 - 3 * p.x * t * p.z) p.y =
        deriv (fun t : ℝ => 1 * t ^ 3 + 0 * t ^ 2 + (-3 * p.x * p.z) * t +
          (p.x ^ 3 + p.z ^ 3)) p.y := by
      apply congrArg (fun f : ℝ → ℝ => deriv f p.y)
      funext t
      ring
    _ = 3 * 1 * p.y ^ 2 + 2 * 0 * p.y + (-3 * p.x * p.z) :=
      deriv_cubic_polynomial 1 0 (-3 * p.x * p.z) (p.x ^ 3 + p.z ^ 3) p.y
    _ = 3 * p.y ^ 2 - 3 * p.x * p.z := by ring

theorem gap3 :
    ∀ p : Point3,
      partialZ polynomial p = 3 * p.z ^ 2 - 3 * p.x * p.y := by
  intro p
  simp only [partialZ, polynomial]
  calc
    deriv (fun t : ℝ => p.x ^ 3 + p.y ^ 3 + t ^ 3 - 3 * p.x * p.y * t) p.z =
        deriv (fun t : ℝ => 1 * t ^ 3 + 0 * t ^ 2 + (-3 * p.x * p.y) * t +
          (p.x ^ 3 + p.y ^ 3)) p.z := by
      apply congrArg (fun f : ℝ → ℝ => deriv f p.z)
      funext t
      ring
    _ = 3 * 1 * p.z ^ 2 + 2 * 0 * p.z + (-3 * p.x * p.y) :=
      deriv_cubic_polynomial 1 0 (-3 * p.x * p.y) (p.x ^ 3 + p.y ^ 3) p.z
    _ = 3 * p.z ^ 2 - 3 * p.x * p.y := by ring

theorem gap4 :
    ∀ p : Point3, partialXX polynomial p = 6 * p.x := by
  intro p
  change deriv (fun t : ℝ => partialX polynomial ⟨t, p.y, p.z⟩) p.x = 6 * p.x
  simp_rw [gap1]
  calc
    deriv (fun t : ℝ => 3 * t ^ 2 - 3 * p.y * p.z) p.x =
        deriv (fun t : ℝ => 0 * t ^ 3 + 3 * t ^ 2 + 0 * t + (-3 * p.y * p.z)) p.x := by
      apply congrArg (fun f : ℝ → ℝ => deriv f p.x)
      funext t
      ring
    _ = 3 * 0 * p.x ^ 2 + 2 * 3 * p.x + 0 :=
      deriv_cubic_polynomial 0 3 0 (-3 * p.y * p.z) p.x
    _ = 6 * p.x := by ring

theorem gap5 :
    ∀ p : Point3, partialYY polynomial p = 6 * p.y := by
  intro p
  change deriv (fun t : ℝ => partialY polynomial ⟨p.x, t, p.z⟩) p.y = 6 * p.y
  simp_rw [gap2]
  calc
    deriv (fun t : ℝ => 3 * t ^ 2 - 3 * p.x * p.z) p.y =
        deriv (fun t : ℝ => 0 * t ^ 3 + 3 * t ^ 2 + 0 * t + (-3 * p.x * p.z)) p.y := by
      apply congrArg (fun f : ℝ → ℝ => deriv f p.y)
      funext t
      ring
    _ = 3 * 0 * p.y ^ 2 + 2 * 3 * p.y + 0 :=
      deriv_cubic_polynomial 0 3 0 (-3 * p.x * p.z) p.y
    _ = 6 * p.y := by ring

theorem gap6 :
    ∀ p : Point3, partialZZ polynomial p = 6 * p.z := by
  intro p
  change deriv (fun t : ℝ => partialZ polynomial ⟨p.x, p.y, t⟩) p.z = 6 * p.z
  simp_rw [gap3]
  calc
    deriv (fun t : ℝ => 3 * t ^ 2 - 3 * p.x * p.y) p.z =
        deriv (fun t : ℝ => 0 * t ^ 3 + 3 * t ^ 2 + 0 * t + (-3 * p.x * p.y)) p.z := by
      apply congrArg (fun f : ℝ → ℝ => deriv f p.z)
      funext t
      ring
    _ = 3 * 0 * p.z ^ 2 + 2 * 3 * p.z + 0 :=
      deriv_cubic_polynomial 0 3 0 (-3 * p.x * p.y) p.z
    _ = 6 * p.z := by ring

theorem gap7 :
    ∀ p : Point3, partialXY polynomial p = -3 * p.z := by
  intro p
  change deriv (fun t : ℝ => partialX polynomial ⟨p.x, t, p.z⟩) p.y = -3 * p.z
  simp_rw [gap1]
  calc
    deriv (fun t : ℝ => 3 * p.x ^ 2 - 3 * t * p.z) p.y =
        deriv (fun t : ℝ => 0 * t ^ 3 + 0 * t ^ 2 + (-3 * p.z) * t + 3 * p.x ^ 2) p.y := by
      apply congrArg (fun f : ℝ → ℝ => deriv f p.y)
      funext t
      ring
    _ = 3 * 0 * p.y ^ 2 + 2 * 0 * p.y + (-3 * p.z) :=
      deriv_cubic_polynomial 0 0 (-3 * p.z) (3 * p.x ^ 2) p.y
    _ = -3 * p.z := by ring

theorem gap8 :
    ∀ p : Point3, partialYZ polynomial p = -3 * p.x := by
  intro p
  change deriv (fun t : ℝ => partialY polynomial ⟨p.x, p.y, t⟩) p.z = -3 * p.x
  simp_rw [gap2]
  calc
    deriv (fun t : ℝ => 3 * p.y ^ 2 - 3 * p.x * t) p.z =
        deriv (fun t : ℝ => 0 * t ^ 3 + 0 * t ^ 2 + (-3 * p.x) * t + 3 * p.y ^ 2) p.z := by
      apply congrArg (fun f : ℝ → ℝ => deriv f p.z)
      funext t
      ring
    _ = 3 * 0 * p.z ^ 2 + 2 * 0 * p.z + (-3 * p.x) :=
      deriv_cubic_polynomial 0 0 (-3 * p.x) (3 * p.y ^ 2) p.z
    _ = -3 * p.x := by ring

theorem gap9 :
    ∀ p : Point3, partialXZ polynomial p = -3 * p.y := by
  intro p
  change deriv (fun t : ℝ => partialX polynomial ⟨p.x, p.y, t⟩) p.z = -3 * p.y
  simp_rw [gap1]
  calc
    deriv (fun t : ℝ => 3 * p.x ^ 2 - 3 * p.y * t) p.z =
        deriv (fun t : ℝ => 0 * t ^ 3 + 0 * t ^ 2 + (-3 * p.y) * t + 3 * p.x ^ 2) p.z := by
      apply congrArg (fun f : ℝ → ℝ => deriv f p.z)
      funext t
      ring
    _ = 3 * 0 * p.z ^ 2 + 2 * 0 * p.z + (-3 * p.y) :=
      deriv_cubic_polynomial 0 0 (-3 * p.y) (3 * p.x ^ 2) p.z
    _ = -3 * p.y := by ring

theorem gap10 :
    ∀ p : Point3, partialXXX polynomial p = partialYYY polynomial p := by
  intro p
  have hx : partialXXX polynomial p = 6 := by
    change deriv (fun t : ℝ => partialXX polynomial ⟨t, p.y, p.z⟩) p.x = 6
    simp_rw [gap4]
    calc
      deriv (fun t : ℝ => 6 * t) p.x =
          deriv (fun t : ℝ => 0 * t ^ 3 + 0 * t ^ 2 + 6 * t + 0) p.x := by
        apply congrArg (fun f : ℝ → ℝ => deriv f p.x)
        funext t
        ring
      _ = 3 * 0 * p.x ^ 2 + 2 * 0 * p.x + 6 :=
        deriv_cubic_polynomial 0 0 6 0 p.x
      _ = 6 := by ring
  have hy : partialYYY polynomial p = 6 := by
    change deriv (fun t : ℝ => partialYY polynomial ⟨p.x, t, p.z⟩) p.y = 6
    simp_rw [gap5]
    calc
      deriv (fun t : ℝ => 6 * t) p.y =
          deriv (fun t : ℝ => 0 * t ^ 3 + 0 * t ^ 2 + 6 * t + 0) p.y := by
        apply congrArg (fun f : ℝ → ℝ => deriv f p.y)
        funext t
        ring
      _ = 3 * 0 * p.y ^ 2 + 2 * 0 * p.y + 6 :=
        deriv_cubic_polynomial 0 0 6 0 p.y
      _ = 6 := by ring
  exact hx.trans hy.symm

theorem gap11 :
    ∀ p : Point3, partialYYY polynomial p = partialZZZ polynomial p := by
  intro p
  have hy : partialYYY polynomial p = 6 := by
    change deriv (fun t : ℝ => partialYY polynomial ⟨p.x, t, p.z⟩) p.y = 6
    simp_rw [gap5]
    calc
      deriv (fun t : ℝ => 6 * t) p.y =
          deriv (fun t : ℝ => 0 * t ^ 3 + 0 * t ^ 2 + 6 * t + 0) p.y := by
        apply congrArg (fun f : ℝ → ℝ => deriv f p.y)
        funext t
        ring
      _ = 3 * 0 * p.y ^ 2 + 2 * 0 * p.y + 6 :=
        deriv_cubic_polynomial 0 0 6 0 p.y
      _ = 6 := by ring
  have hz : partialZZZ polynomial p = 6 := by
    change deriv (fun t : ℝ => partialZZ polynomial ⟨p.x, p.y, t⟩) p.z = 6
    simp_rw [gap6]
    calc
      deriv (fun t : ℝ => 6 * t) p.z =
          deriv (fun t : ℝ => 0 * t ^ 3 + 0 * t ^ 2 + 6 * t + 0) p.z := by
        apply congrArg (fun f : ℝ → ℝ => deriv f p.z)
        funext t
        ring
      _ = 3 * 0 * p.z ^ 2 + 2 * 0 * p.z + 6 :=
        deriv_cubic_polynomial 0 0 6 0 p.z
      _ = 6 := by ring
  exact hy.trans hz.symm

theorem gap12 :
    ∀ p : Point3, partialZZZ polynomial p = 6 := by
  intro p
  change deriv (fun t : ℝ => partialZZ polynomial ⟨p.x, p.y, t⟩) p.z = 6
  simp_rw [gap6]
  calc
    deriv (fun t : ℝ => 6 * t) p.z =
        deriv (fun t : ℝ => 0 * t ^ 3 + 0 * t ^ 2 + 6 * t + 0) p.z := by
      apply congrArg (fun f : ℝ → ℝ => deriv f p.z)
      funext t
      ring
    _ = 3 * 0 * p.z ^ 2 + 2 * 0 * p.z + 6 :=
      deriv_cubic_polynomial 0 0 6 0 p.z
    _ = 6 := by ring

theorem gap13 :
    ∀ p : Point3, partialXYZ polynomial p = -3 := by
  intro p
  change deriv (fun t : ℝ => partialXY polynomial ⟨p.x, p.y, t⟩) p.z = -3
  simp_rw [gap7]
  calc
    deriv (fun t : ℝ => -3 * t) p.z =
        deriv (fun t : ℝ => 0 * t ^ 3 + 0 * t ^ 2 + (-3) * t + 0) p.z := by
      apply congrArg (fun f : ℝ → ℝ => deriv f p.z)
      funext t
      ring
    _ = 3 * 0 * p.z ^ 2 + 2 * 0 * p.z + (-3) :=
      deriv_cubic_polynomial 0 0 (-3) 0 p.z
    _ = -3 := by ring

theorem gap14 :
    ∀ p : Point3, remainder3 p = 0 := by
  intro p
  simp only [remainder3, polynomial, taylorPolynomial3]
  ring

theorem gap15 :
    polynomial basePoint = 0 := by
  norm_num [polynomial, basePoint]

theorem gap16 :
    partialX polynomial basePoint = partialY polynomial basePoint := by
  simp [gap1, gap2, basePoint]

theorem gap17 :
    partialY polynomial basePoint = partialZ polynomial basePoint := by
  simp [gap2, gap3, basePoint]

theorem gap18 :
    partialZ polynomial basePoint = 0 := by
  simp [gap3, basePoint]

theorem gap19 :
    ∀ p : Point3, polynomial p = taylorPolynomial3 p := by
  intro p
  apply sub_eq_zero.mp
  simpa [remainder3] using gap14 p

theorem gap20 :
    ∀ p : Point3,
      polynomial p =
        3 * ((p.x - 1) ^ 2 + (p.y - 1) ^ 2 + (p.z - 1) ^ 2 -
          (p.x - 1) * (p.y - 1) - (p.x - 1) * (p.z - 1) -
          (p.y - 1) * (p.z - 1)) +
        (p.x - 1) ^ 3 + (p.y - 1) ^ 3 + (p.z - 1) ^ 3 -
        3 * (p.x - 1) * (p.y - 1) * (p.z - 1) := by
  intro p
  simpa [taylorPolynomial3] using gap19 p

end

end ProofGap.Exercise3582
