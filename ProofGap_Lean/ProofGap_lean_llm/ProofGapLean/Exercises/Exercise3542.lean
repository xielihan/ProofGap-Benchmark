import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3542

noncomputable section

abbrev Point3 := ℝ × (ℝ × ℝ)

def quadricValue (a b c : ℝ) (P : Point3) : ℝ :=
  a * P.1 ^ 2 + b * P.2.1 ^ 2 + c * P.2.2 ^ 2

def basePoint (x0 y0 z0 : ℝ) : Point3 := (x0, (y0, z0))

def normalDirection (a b c x0 y0 z0 : ℝ) : Point3 :=
  (a * x0, (b * y0, c * z0))

def scale (r : ℝ) (V : Point3) : Point3 :=
  (r * V.1, (r * V.2.1, r * V.2.2))

def gradientAt (a b c : ℝ) (P : Point3) : Point3 :=
  (2 * a * P.1, (2 * b * P.2.1, 2 * c * P.2.2))

def OnSurface (a b c : ℝ) (P : Point3) : Prop :=
  quadricValue a b c P = 1

def dot (U V : Point3) : ℝ :=
  U.1 * V.1 + U.2.1 * V.2.1 + U.2.2 * V.2.2

def displacement (Q P : Point3) : Point3 :=
  (Q.1 - P.1, (Q.2.1 - P.2.1, Q.2.2 - P.2.2))

def planeFromPointNormal (P N : Point3) : Set Point3 :=
  {Q | dot N (displacement Q P) = 0}

def tangentPlane (a b c x0 y0 z0 : ℝ) : Set Point3 :=
  planeFromPointNormal (basePoint x0 y0 z0)
    (normalDirection a b c x0 y0 z0)

def simplifiedPlane (a b c x0 y0 z0 : ℝ) : Set Point3 :=
  {Q | a * x0 * Q.1 + b * y0 * Q.2.1 + c * z0 * Q.2.2 = 1}

def linePoint (P V : Point3) (s : ℝ) : Point3 :=
  (P.1 + s * V.1, (P.2.1 + s * V.2.1, P.2.2 + s * V.2.2))

def normalLine (a b c x0 y0 z0 : ℝ) : Set Point3 :=
  {Q |
    ∃ s : ℝ,
      Q = linePoint (basePoint x0 y0 z0)
        (normalDirection a b c x0 y0 z0) s}

theorem gap1 (a b c x0 y0 z0 : ℝ) :
    gradientAt a b c (basePoint x0 y0 z0) =
      scale 2 (normalDirection a b c x0 y0 z0) := by
  simp [gradientAt, basePoint, scale, normalDirection, mul_assoc]

theorem gap2 (a b c x0 y0 z0 : ℝ) :
    tangentPlane a b c x0 y0 z0 =
      {Q |
        a * x0 * (Q.1 - x0) + b * y0 * (Q.2.1 - y0) +
          c * z0 * (Q.2.2 - z0) = 0} := by
  rfl

theorem gap3 (a b c x0 y0 z0 : ℝ)
    (hM : OnSurface a b c (basePoint x0 y0 z0)) :
    a * x0 ^ 2 + b * y0 ^ 2 + c * z0 ^ 2 = 1 := by
  simpa [OnSurface, quadricValue, basePoint] using hM

theorem gap4 (a b c x0 y0 z0 : ℝ)
    (hM : OnSurface a b c (basePoint x0 y0 z0)) :
    tangentPlane a b c x0 y0 z0 =
      simplifiedPlane a b c x0 y0 z0 := by
  rw [gap2]
  apply Set.ext
  intro Q
  change
    (a * x0 * (Q.1 - x0) + b * y0 * (Q.2.1 - y0) +
        c * z0 * (Q.2.2 - z0) = 0) ↔
      (a * x0 * Q.1 + b * y0 * Q.2.1 + c * z0 * Q.2.2 = 1)
  have hsurface := gap3 a b c x0 y0 z0 hM
  constructor <;> intro hQ <;> nlinarith

theorem gap5 (a b c x0 y0 z0 : ℝ)
    (hM : OnSurface a b c (basePoint x0 y0 z0)) :
    normalLine a b c x0 y0 z0 =
      {Q |
        (Q.1 - x0) * (b * y0) = (Q.2.1 - y0) * (a * x0) ∧
        (Q.2.1 - y0) * (c * z0) = (Q.2.2 - z0) * (b * y0) ∧
        (Q.1 - x0) * (c * z0) = (Q.2.2 - z0) * (a * x0)} := by
  apply Set.ext
  intro Q
  change
    (∃ s : ℝ,
      Q = linePoint (basePoint x0 y0 z0)
        (normalDirection a b c x0 y0 z0) s) ↔
      ((Q.1 - x0) * (b * y0) = (Q.2.1 - y0) * (a * x0) ∧
       (Q.2.1 - y0) * (c * z0) = (Q.2.2 - z0) * (b * y0) ∧
       (Q.1 - x0) * (c * z0) = (Q.2.2 - z0) * (a * x0))
  constructor
  · rintro ⟨s, rfl⟩
    dsimp [linePoint, basePoint, normalDirection]
    constructor
    · ring
    constructor <;> ring
  · rintro ⟨hxy, hyz, hxz⟩
    rcases Q with ⟨qx, qy, qz⟩
    change (qx - x0) * (b * y0) = (qy - y0) * (a * x0) at hxy
    change (qy - y0) * (c * z0) = (qz - z0) * (b * y0) at hyz
    change (qx - x0) * (c * z0) = (qz - z0) * (a * x0) at hxz
    have hn :
        a * x0 ≠ 0 ∨ b * y0 ≠ 0 ∨ c * z0 ≠ 0 := by
      by_cases hA : a * x0 = 0
      · by_cases hB : b * y0 = 0
        · by_cases hC : c * z0 = 0
          · have hv := gap3 a b c x0 y0 z0 hM
            norm_num [pow_two, ← mul_assoc, hA, hB, hC] at hv
          · exact Or.inr (Or.inr hC)
        · exact Or.inr (Or.inl hB)
      · exact Or.inl hA
    rcases hn with hA | hB | hC
    · let s := (qx - x0) / (a * x0)
      have hsx : s * (a * x0) = qx - x0 := by
        dsimp [s]
        exact div_mul_cancel₀ _ hA
      have hsy : s * (b * y0) = qy - y0 := by
        dsimp [s]
        calc
          (qx - x0) / (a * x0) * (b * y0) =
              ((qx - x0) * (b * y0)) / (a * x0) := by
                rw [div_mul_eq_mul_div]
          _ = qy - y0 := (div_eq_iff hA).2 hxy
      have hsz : s * (c * z0) = qz - z0 := by
        dsimp [s]
        calc
          (qx - x0) / (a * x0) * (c * z0) =
              ((qx - x0) * (c * z0)) / (a * x0) := by
                rw [div_mul_eq_mul_div]
          _ = qz - z0 := (div_eq_iff hA).2 hxz
      refine ⟨s, ?_⟩
      apply Prod.ext
      · change qx = x0 + s * (a * x0)
        rw [hsx]
        ring
      · apply Prod.ext
        · change qy = y0 + s * (b * y0)
          rw [hsy]
          ring
        · change qz = z0 + s * (c * z0)
          rw [hsz]
          ring
    · let s := (qy - y0) / (b * y0)
      have hsx : s * (a * x0) = qx - x0 := by
        dsimp [s]
        calc
          (qy - y0) / (b * y0) * (a * x0) =
              ((qy - y0) * (a * x0)) / (b * y0) := by
                rw [div_mul_eq_mul_div]
          _ = qx - x0 := (div_eq_iff hB).2 hxy.symm
      have hsy : s * (b * y0) = qy - y0 := by
        dsimp [s]
        exact div_mul_cancel₀ _ hB
      have hsz : s * (c * z0) = qz - z0 := by
        dsimp [s]
        calc
          (qy - y0) / (b * y0) * (c * z0) =
              ((qy - y0) * (c * z0)) / (b * y0) := by
                rw [div_mul_eq_mul_div]
          _ = qz - z0 := (div_eq_iff hB).2 hyz
      refine ⟨s, ?_⟩
      apply Prod.ext
      · change qx = x0 + s * (a * x0)
        rw [hsx]
        ring
      · apply Prod.ext
        · change qy = y0 + s * (b * y0)
          rw [hsy]
          ring
        · change qz = z0 + s * (c * z0)
          rw [hsz]
          ring
    · let s := (qz - z0) / (c * z0)
      have hsx : s * (a * x0) = qx - x0 := by
        dsimp [s]
        calc
          (qz - z0) / (c * z0) * (a * x0) =
              ((qz - z0) * (a * x0)) / (c * z0) := by
                rw [div_mul_eq_mul_div]
          _ = qx - x0 := (div_eq_iff hC).2 hxz.symm
      have hsy : s * (b * y0) = qy - y0 := by
        dsimp [s]
        calc
          (qz - z0) / (c * z0) * (b * y0) =
              ((qz - z0) * (b * y0)) / (c * z0) := by
                rw [div_mul_eq_mul_div]
          _ = qy - y0 := (div_eq_iff hC).2 hyz.symm
      have hsz : s * (c * z0) = qz - z0 := by
        dsimp [s]
        exact div_mul_cancel₀ _ hC
      refine ⟨s, ?_⟩
      apply Prod.ext
      · change qx = x0 + s * (a * x0)
        rw [hsx]
        ring
      · apply Prod.ext
        · change qy = y0 + s * (b * y0)
          rw [hsy]
          ring
        · change qz = z0 + s * (c * z0)
          rw [hsz]
          ring

end

end ProofGap.Exercise3542
