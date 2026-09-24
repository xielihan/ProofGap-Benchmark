import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3564

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def quadraticField (p : Point3) : ℝ :=
  p.x ^ 2 + p.y ^ 2 + p.z ^ 2

def ellipsoidLevel (a b c : ℝ) (p : Point3) : ℝ :=
  p.x ^ 2 / a ^ 2 + p.y ^ 2 / b ^ 2 + p.z ^ 2 / c ^ 2

def ellipsoid (a b c : ℝ) : Set Point3 :=
  {p | ellipsoidLevel a b c p = 1}

def ellipsoidNormal (a b c : ℝ) (p : Point3) : Point3 :=
  ⟨deriv (fun t => ellipsoidLevel a b c ⟨t, p.y, p.z⟩) p.x,
    deriv (fun t => ellipsoidLevel a b c ⟨p.x, t, p.z⟩) p.y,
    deriv (fun t => ellipsoidLevel a b c ⟨p.x, p.y, t⟩) p.z⟩

def delta (a b c : ℝ) (p : Point3) : ℝ :=
  Real.sqrt
    (p.x ^ 2 / a ^ 4 + p.y ^ 2 / b ^ 4 + p.z ^ 2 / c ^ 4)

def unitNormal (a b c : ℝ) (p : Point3) : Point3 :=
  ⟨(ellipsoidNormal a b c p).x / (2 * delta a b c p),
    (ellipsoidNormal a b c p).y / (2 * delta a b c p),
    (ellipsoidNormal a b c p).z / (2 * delta a b c p)⟩

def directionalDerivative (f : Point3 → ℝ) (p v : Point3) : ℝ :=
  deriv
    (fun t => f ⟨p.x + t * v.x, p.y + t * v.y, p.z + t * v.z⟩) 0

private theorem point3_eq_of_coordinates {p q : Point3}
    (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) : p = q := by
  cases p with
  | mk px py pz =>
    cases q with
    | mk qx qy qz =>
      dsimp at hx hy hz
      cases hx
      cases hy
      cases hz
      rfl

theorem gap1 (a b c : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∀ p : Point3, p ∈ ellipsoid a b c →
      unitNormal a b c p =
        ⟨p.x / (a ^ 2 * delta a b c p),
          p.y / (b ^ 2 * delta a b c p),
          p.z / (c ^ 2 * delta a b c p)⟩ := by
  intro p _
  have hsq (x : ℝ) :
      HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa [pow_two, two_mul] using
      (hasDerivAt_id x).mul (hasDerivAt_id x)
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  apply point3_eq_of_coordinates
  · change
      deriv (fun t : ℝ => ellipsoidLevel a b c ⟨t, p.y, p.z⟩) p.x /
          (2 * delta a b c p) =
        p.x / (a ^ 2 * delta a b c p)
    have hx :
        HasDerivAt
          (fun t : ℝ => ellipsoidLevel a b c ⟨t, p.y, p.z⟩)
          (2 * p.x / a ^ 2) p.x := by
      simpa [ellipsoidLevel, div_eq_mul_inv] using
        (((hsq p.x).mul_const (a ^ 2)⁻¹).add_const
          (p.y ^ 2 / b ^ 2)).add_const (p.z ^ 2 / c ^ 2)
    rw [hx.deriv]
    by_cases hδ : delta a b c p = 0
    · simp [hδ]
    · field_simp [ha2, hδ] <;> ring
  · change
      deriv (fun t : ℝ => ellipsoidLevel a b c ⟨p.x, t, p.z⟩) p.y /
          (2 * delta a b c p) =
        p.y / (b ^ 2 * delta a b c p)
    have hy :
        HasDerivAt
          (fun t : ℝ => ellipsoidLevel a b c ⟨p.x, t, p.z⟩)
          (2 * p.y / b ^ 2) p.y := by
      simpa [ellipsoidLevel, div_eq_mul_inv] using
        (((hsq p.y).mul_const (b ^ 2)⁻¹).const_add
          (p.x ^ 2 / a ^ 2)).add_const (p.z ^ 2 / c ^ 2)
    rw [hy.deriv]
    by_cases hδ : delta a b c p = 0
    · simp [hδ]
    · field_simp [hb2, hδ] <;> ring
  · change
      deriv (fun t : ℝ => ellipsoidLevel a b c ⟨p.x, p.y, t⟩) p.z /
          (2 * delta a b c p) =
        p.z / (c ^ 2 * delta a b c p)
    have hz :
        HasDerivAt
          (fun t : ℝ => ellipsoidLevel a b c ⟨p.x, p.y, t⟩)
          (2 * p.z / c ^ 2) p.z := by
      simpa [ellipsoidLevel, div_eq_mul_inv] using
        ((hsq p.z).mul_const (c ^ 2)⁻¹).const_add
          (p.x ^ 2 / a ^ 2 + p.y ^ 2 / b ^ 2)
    rw [hz.deriv]
    by_cases hδ : delta a b c p = 0
    · simp [hδ]
    · field_simp [hc2, hδ] <;> ring

theorem gap2 (a b c : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∀ p : Point3, p ∈ ellipsoid a b c →
      directionalDerivative quadraticField p (unitNormal a b c p) =
        p.x / (a ^ 2 * delta a b c p) * (2 * p.x) +
          p.y / (b ^ 2 * delta a b c p) * (2 * p.y) +
          p.z / (c ^ 2 * delta a b c p) * (2 * p.z) := by
  intro p hp
  have hquad (v : Point3) :
      directionalDerivative quadraticField p v =
        v.x * (2 * p.x) + v.y * (2 * p.y) + v.z * (2 * p.z) := by
    change
      deriv
          (fun t : ℝ =>
            (p.x + t * v.x) ^ 2 + (p.y + t * v.y) ^ 2 +
              (p.z + t * v.z) ^ 2)
          0 =
        v.x * (2 * p.x) + v.y * (2 * p.y) + v.z * (2 * p.z)
    have hx : HasDerivAt (fun t : ℝ => p.x + t * v.x) v.x 0 := by
      simpa using
        ((hasDerivAt_id (0 : ℝ)).mul_const v.x).const_add p.x
    have hy : HasDerivAt (fun t : ℝ => p.y + t * v.y) v.y 0 := by
      simpa using
        ((hasDerivAt_id (0 : ℝ)).mul_const v.y).const_add p.y
    have hz : HasDerivAt (fun t : ℝ => p.z + t * v.z) v.z 0 := by
      simpa using
        ((hasDerivAt_id (0 : ℝ)).mul_const v.z).const_add p.z
    simp only [pow_two]
    convert (((hx.mul hx).add (hy.mul hy)).add (hz.mul hz)).deriv using 1 <;>
      norm_num <;> ring
  rw [hquad (unitNormal a b c p), gap1 a b c ha hb hc p hp]

theorem gap3 (a b c : ℝ) :
    ∀ p : Point3, delta a b c p ≠ 0 →
      p.x / (a ^ 2 * delta a b c p) * (2 * p.x) +
          p.y / (b ^ 2 * delta a b c p) * (2 * p.y) +
          p.z / (c ^ 2 * delta a b c p) * (2 * p.z) =
        (2 / delta a b c p) * ellipsoidLevel a b c p := by
  intro p hδ
  have hx :
      p.x / (a ^ 2 * delta a b c p) * (2 * p.x) =
        (2 / delta a b c p) * (p.x ^ 2 / a ^ 2) := by
    by_cases ha0 : a = 0
    · simp [ha0]
    · have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha0
      field_simp [ha2, hδ] <;> ring
  have hy :
      p.y / (b ^ 2 * delta a b c p) * (2 * p.y) =
        (2 / delta a b c p) * (p.y ^ 2 / b ^ 2) := by
    by_cases hb0 : b = 0
    · simp [hb0]
    · have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb0
      field_simp [hb2, hδ] <;> ring
  have hz :
      p.z / (c ^ 2 * delta a b c p) * (2 * p.z) =
        (2 / delta a b c p) * (p.z ^ 2 / c ^ 2) := by
    by_cases hc0 : c = 0
    · simp [hc0]
    · have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0
      field_simp [hc2, hδ] <;> ring
  rw [hx, hy, hz]
  unfold ellipsoidLevel
  ring

theorem gap4 (a b c : ℝ) :
    ∀ p : Point3, p ∈ ellipsoid a b c →
      (2 / delta a b c p) * ellipsoidLevel a b c p =
        2 / delta a b c p := by
  intro p hp
  change ellipsoidLevel a b c p = 1 at hp
  simp [hp]

theorem gap5 (a b c : ℝ) :
    ∀ p : Point3,
      2 / delta a b c p =
        2 / Real.sqrt
          (p.x ^ 2 / a ^ 4 + p.y ^ 2 / b ^ 4 +
            p.z ^ 2 / c ^ 4) := by
  intro p
  rfl

theorem gap6 (a b c : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∀ p : Point3, p ∈ ellipsoid a b c →
      directionalDerivative quadraticField p (unitNormal a b c p) =
        2 / Real.sqrt
          (p.x ^ 2 / a ^ 4 + p.y ^ 2 / b ^ 4 +
            p.z ^ 2 / c ^ 4) := by
  intro p hp
  by_cases hδ : delta a b c p = 0
  · rw [gap2 a b c ha hb hc p hp]
    rw [← gap5 a b c p]
    simp [hδ]
  · calc
      directionalDerivative quadraticField p (unitNormal a b c p) =
          p.x / (a ^ 2 * delta a b c p) * (2 * p.x) +
            p.y / (b ^ 2 * delta a b c p) * (2 * p.y) +
            p.z / (c ^ 2 * delta a b c p) * (2 * p.z) :=
        gap2 a b c ha hb hc p hp
      _ = (2 / delta a b c p) * ellipsoidLevel a b c p :=
        gap3 a b c p hδ
      _ = 2 / delta a b c p := gap4 a b c p hp
      _ =
          2 / Real.sqrt
            (p.x ^ 2 / a ^ 4 + p.y ^ 2 / b ^ 4 +
              p.z ^ 2 / c ^ 4) := gap5 a b c p

end

end ProofGap.Exercise3564
