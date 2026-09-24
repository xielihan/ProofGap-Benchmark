import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace ProofGap.Exercise3536

noncomputable section

abbrev Point3 := ℝ × (ℝ × ℝ)

def dot (U V : Point3) : ℝ :=
  U.1 * V.1 + U.2.1 * V.2.1 + U.2.2 * V.2.2

def norm3 (V : Point3) : ℝ :=
  Real.sqrt (V.1 ^ 2 + V.2.1 ^ 2 + V.2.2 ^ 2)

def scale (c : ℝ) (V : Point3) : Point3 :=
  (c * V.1, (c * V.2.1, c * V.2.2))

def mercatorRelation (k : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ ψ, Real.tan (Real.pi / 4 + ψ / 2) = Real.exp (k * φ ψ)

def curve (R : ℝ) (φ : ℝ → ℝ) (ψ : ℝ) : Point3 :=
  (R * Real.cos ψ * Real.cos (φ ψ),
    (R * Real.cos ψ * Real.sin (φ ψ), R * Real.sin ψ))

def tangent (R : ℝ) (φ : ℝ → ℝ) (ψ : ℝ) : Point3 :=
  (deriv (fun s => (curve R φ s).1) ψ,
    (deriv (fun s => (curve R φ s).2.1) ψ,
      deriv (fun s => (curve R φ s).2.2) ψ))

def curveDirection (k : ℝ) (φ : ℝ → ℝ) (ψ : ℝ) : Point3 :=
  (Real.sin ψ * Real.cos (φ ψ) + Real.sin (φ ψ) / k,
    (Real.sin ψ * Real.sin (φ ψ) - Real.cos (φ ψ) / k,
      -Real.cos ψ))

def meridianDirection (φ0 ψ : ℝ) : Point3 :=
  (Real.sin ψ * Real.cos φ0,
    (Real.sin ψ * Real.sin φ0, -Real.cos ψ))

def angleCos (k φ0 ψ : ℝ) : ℝ :=
  dot (curveDirection k (fun _ => φ0) ψ) (meridianDirection φ0 ψ) /
    (norm3 (curveDirection k (fun _ => φ0) ψ) *
      norm3 (meridianDirection φ0 ψ))

theorem gap1 (R : ℝ) (φ : ℝ → ℝ) :
    ∀ ψ, (curve R φ ψ).1 = R * Real.cos ψ * Real.cos (φ ψ) := by
  intro ψ
  rfl

theorem gap2 (R : ℝ) (φ : ℝ → ℝ) :
    ∀ ψ, (curve R φ ψ).2.1 = R * Real.cos ψ * Real.sin (φ ψ) := by
  intro ψ
  rfl

theorem gap3 (R : ℝ) (φ : ℝ → ℝ) :
    ∀ ψ, (curve R φ ψ).2.2 = R * Real.sin ψ := by
  intro ψ
  rfl

theorem gap4 (k : ℝ) (φ : ℝ → ℝ) (ψ : ℝ)
    (hRel : mercatorRelation k φ)
    (hDiff : DifferentiableAt ℝ φ ψ) :
    1 / (2 * Real.cos (Real.pi / 4 + ψ / 2) ^ 2) =
      k * Real.exp (k * φ ψ) * deriv φ ψ := by
  have hcx : Real.cos (Real.pi / 4 + ψ / 2) ≠ 0 := by
    intro hc
    have ht : Real.tan (Real.pi / 4 + ψ / 2) = 0 := by
      simp [Real.tan_eq_sin_div_cos, hc]
    have h := hRel ψ
    rw [ht] at h
    exact Real.exp_ne_zero _ h.symm
  have hinner :
      HasDerivAt (fun s : ℝ => Real.pi / 4 + s / 2) (1 / 2) ψ := by
    exact ((hasDerivAt_id ψ).div_const 2).const_add (Real.pi / 4)
  have htan :
      HasDerivAt Real.tan
        (1 / Real.cos (Real.pi / 4 + ψ / 2) ^ 2)
        (Real.pi / 4 + ψ / 2) :=
    Real.hasDerivAt_tan hcx
  have hleft :
      HasDerivAt
        (fun s : ℝ => Real.tan (Real.pi / 4 + s / 2))
        ((1 / Real.cos (Real.pi / 4 + ψ / 2) ^ 2) * (1 / 2)) ψ := by
    simpa only [Function.comp_apply] using htan.comp ψ hinner
  have hkφ :
      HasDerivAt (fun s : ℝ => k * φ s) (k * deriv φ ψ) ψ :=
    hDiff.hasDerivAt.const_mul k
  have hexp :
      HasDerivAt Real.exp (Real.exp (k * φ ψ)) (k * φ ψ) :=
    Real.hasDerivAt_exp (k * φ ψ)
  have hright :
      HasDerivAt
        (fun s : ℝ => Real.exp (k * φ s))
        (Real.exp (k * φ ψ) * (k * deriv φ ψ)) ψ := by
    simpa only [Function.comp_apply] using hexp.comp ψ hkφ
  have heq :
      (fun s : ℝ => Real.tan (Real.pi / 4 + s / 2)) =
        fun s : ℝ => Real.exp (k * φ s) := by
    funext s
    exact hRel s
  calc
    1 / (2 * Real.cos (Real.pi / 4 + ψ / 2) ^ 2) =
        (1 / Real.cos (Real.pi / 4 + ψ / 2) ^ 2) * (1 / 2) := by
          field_simp [hcx] <;> ring
    _ = deriv (fun s : ℝ => Real.tan (Real.pi / 4 + s / 2)) ψ :=
      hleft.deriv.symm
    _ = deriv (fun s : ℝ => Real.exp (k * φ s)) ψ := by rw [heq]
    _ = Real.exp (k * φ ψ) * (k * deriv φ ψ) := hright.deriv
    _ = k * Real.exp (k * φ ψ) * deriv φ ψ := by ring

theorem gap5 (k : ℝ) (φ : ℝ → ℝ) (ψ : ℝ)
    (hRel : mercatorRelation k φ) :
    k * Real.exp (k * φ ψ) * deriv φ ψ =
      k * Real.tan (Real.pi / 4 + ψ / 2) * deriv φ ψ := by
  rw [← hRel ψ]

theorem gap6 (k : ℝ) (φ : ℝ → ℝ) (ψ : ℝ)
    (hRel : mercatorRelation k φ)
    (hDiff : DifferentiableAt ℝ φ ψ) :
    1 / (2 * Real.cos (Real.pi / 4 + ψ / 2) ^ 2) =
      k * Real.tan (Real.pi / 4 + ψ / 2) * deriv φ ψ := by
  calc
    1 / (2 * Real.cos (Real.pi / 4 + ψ / 2) ^ 2) =
        k * Real.exp (k * φ ψ) * deriv φ ψ :=
      gap4 k φ ψ hRel hDiff
    _ = k * Real.tan (Real.pi / 4 + ψ / 2) * deriv φ ψ :=
      gap5 k φ ψ hRel

theorem gap7 (k : ℝ) (φ : ℝ → ℝ) (ψ : ℝ)
    (hk : k ≠ 0) (hcos : Real.cos ψ ≠ 0)
    (hRel : mercatorRelation k φ)
    (hDiff : DifferentiableAt ℝ φ ψ) :
    deriv φ ψ = 1 / (k * Real.cos ψ) := by
  have hcx : Real.cos (Real.pi / 4 + ψ / 2) ≠ 0 := by
    intro hc
    have ht : Real.tan (Real.pi / 4 + ψ / 2) = 0 := by
      simp [Real.tan_eq_sin_div_cos, hc]
    have h := hRel ψ
    rw [ht] at h
    exact Real.exp_ne_zero _ h.symm
  have htrig :
      2 * Real.cos (Real.pi / 4 + ψ / 2) ^ 2 *
          Real.tan (Real.pi / 4 + ψ / 2) = Real.cos ψ := by
    calc
      2 * Real.cos (Real.pi / 4 + ψ / 2) ^ 2 *
          Real.tan (Real.pi / 4 + ψ / 2) =
          2 * Real.sin (Real.pi / 4 + ψ / 2) *
            Real.cos (Real.pi / 4 + ψ / 2) := by
              rw [Real.tan_eq_sin_div_cos]
              field_simp [hcx] <;> ring
      _ = Real.sin (2 * (Real.pi / 4 + ψ / 2)) :=
        (Real.sin_two_mul (Real.pi / 4 + ψ / 2)).symm
      _ = Real.sin (Real.pi / 2 + ψ) := by
        congr 1
        ring
      _ = Real.cos ψ := by
        rw [Real.sin_add]
        simp
  have hg := gap6 k φ ψ hRel hDiff
  have hden : 2 * Real.cos (Real.pi / 4 + ψ / 2) ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hcx)
  have hbase :
      1 =
        (2 * Real.cos (Real.pi / 4 + ψ / 2) ^ 2) *
          (k * Real.tan (Real.pi / 4 + ψ / 2) * deriv φ ψ) := by
    calc
      1 =
          (2 * Real.cos (Real.pi / 4 + ψ / 2) ^ 2) *
            (1 / (2 * Real.cos (Real.pi / 4 + ψ / 2) ^ 2)) := by
              simpa only [one_div] using (mul_inv_cancel₀ hden).symm
      _ =
          (2 * Real.cos (Real.pi / 4 + ψ / 2) ^ 2) *
            (k * Real.tan (Real.pi / 4 + ψ / 2) * deriv φ ψ) := by
              rw [hg]
  have heq : 1 = k * Real.cos ψ * deriv φ ψ := by
    calc
      1 =
          (2 * Real.cos (Real.pi / 4 + ψ / 2) ^ 2) *
            (k * Real.tan (Real.pi / 4 + ψ / 2) * deriv φ ψ) := hbase
      _ =
          k *
            (2 * Real.cos (Real.pi / 4 + ψ / 2) ^ 2 *
              Real.tan (Real.pi / 4 + ψ / 2)) * deriv φ ψ := by ring
      _ = k * Real.cos ψ * deriv φ ψ := by rw [htrig]
  apply (eq_div_iff (mul_ne_zero hk hcos)).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using heq.symm

theorem gap8 (R k : ℝ) (φ : ℝ → ℝ) (ψ0 : ℝ)
    (hk : k ≠ 0) (hcos : Real.cos ψ0 ≠ 0)
    (hDiff : DifferentiableAt ℝ φ ψ0)
    (hφ : deriv φ ψ0 = 1 / (k * Real.cos ψ0)) :
    deriv (fun s => (curve R φ s).1) ψ0 =
      -R * (Real.sin ψ0 * Real.cos (φ ψ0) +
        Real.sin (φ ψ0) / k) := by
  change
    deriv
        ((fun s : ℝ => R * Real.cos s) * (Real.cos ∘ φ)) ψ0 =
      -R * (Real.sin ψ0 * Real.cos (φ ψ0) + Real.sin (φ ψ0) / k)
  have hd :=
    (((Real.hasDerivAt_cos ψ0).const_mul R).mul
      ((Real.hasDerivAt_cos (φ ψ0)).comp ψ0 hDiff.hasDerivAt)).deriv
  simp only [Function.comp_apply] at hd
  rw [hd, hφ]
  field_simp [hk, hcos] <;> ring

theorem gap9 (R k : ℝ) (φ : ℝ → ℝ) (ψ0 : ℝ)
    (hk : k ≠ 0) (hcos : Real.cos ψ0 ≠ 0)
    (hDiff : DifferentiableAt ℝ φ ψ0)
    (hφ : deriv φ ψ0 = 1 / (k * Real.cos ψ0)) :
    deriv (fun s => (curve R φ s).2.1) ψ0 =
      -R * (Real.sin ψ0 * Real.sin (φ ψ0) -
        Real.cos (φ ψ0) / k) := by
  change
    deriv
        ((fun s : ℝ => R * Real.cos s) * (Real.sin ∘ φ)) ψ0 =
      -R * (Real.sin ψ0 * Real.sin (φ ψ0) - Real.cos (φ ψ0) / k)
  have hd :=
    (((Real.hasDerivAt_cos ψ0).const_mul R).mul
      ((Real.hasDerivAt_sin (φ ψ0)).comp ψ0 hDiff.hasDerivAt)).deriv
  simp only [Function.comp_apply] at hd
  rw [hd, hφ]
  field_simp [hk, hcos] <;> ring

theorem gap10 (R : ℝ) (φ : ℝ → ℝ) :
    ∀ ψ0, deriv (fun s => (curve R φ s).2.2) ψ0 = R * Real.cos ψ0 := by
  intro ψ0
  change deriv (fun s : ℝ => R * Real.sin s) ψ0 = R * Real.cos ψ0
  simpa using ((Real.hasDerivAt_sin ψ0).const_mul R).deriv

theorem gap11 (R k : ℝ) (φ : ℝ → ℝ) (ψ0 : ℝ)
    (hk : k ≠ 0) (hcos : Real.cos ψ0 ≠ 0)
    (hDiff : DifferentiableAt ℝ φ ψ0)
    (hφ : deriv φ ψ0 = 1 / (k * Real.cos ψ0)) :
    tangent R φ ψ0 = scale (-R) (curveDirection k φ ψ0) := by
  unfold tangent scale
  apply Prod.ext
  · change
      deriv (fun s : ℝ => (curve R φ s).1) ψ0 =
        -R * (Real.sin ψ0 * Real.cos (φ ψ0) + Real.sin (φ ψ0) / k)
    exact gap8 R k φ ψ0 hk hcos hDiff hφ
  · apply Prod.ext
    · change
        deriv (fun s : ℝ => (curve R φ s).2.1) ψ0 =
          -R * (Real.sin ψ0 * Real.sin (φ ψ0) - Real.cos (φ ψ0) / k)
      exact gap9 R k φ ψ0 hk hcos hDiff hφ
    · change
        deriv (fun s : ℝ => (curve R φ s).2.2) ψ0 =
          -R * (-Real.cos ψ0)
      rw [gap10 R φ ψ0]
      ring

theorem gap12 (φ0 ψ0 : ℝ) :
    meridianDirection φ0 ψ0 =
      (Real.sin ψ0 * Real.cos φ0,
        (Real.sin ψ0 * Real.sin φ0, -Real.cos ψ0)) := by
  rfl

theorem gap13 (k φ0 ψ0 : ℝ) :
    angleCos k φ0 ψ0 =
      dot (curveDirection k (fun _ => φ0) ψ0) (meridianDirection φ0 ψ0) /
        (norm3 (curveDirection k (fun _ => φ0) ψ0) *
          norm3 (meridianDirection φ0 ψ0)) := by
  rfl

theorem gap14 (k φ0 ψ0 : ℝ) (hk : k ≠ 0) :
    dot (curveDirection k (fun _ => φ0) ψ0) (meridianDirection φ0 ψ0) /
        (norm3 (curveDirection k (fun _ => φ0) ψ0) *
          norm3 (meridianDirection φ0 ψ0)) =
      1 / Real.sqrt (1 + 1 / k ^ 2) := by
  have hdot :
      dot (curveDirection k (fun _ => φ0) ψ0)
          (meridianDirection φ0 ψ0) = 1 := by
    change
      (Real.sin ψ0 * Real.cos φ0 + Real.sin φ0 / k) *
          (Real.sin ψ0 * Real.cos φ0) +
        (Real.sin ψ0 * Real.sin φ0 - Real.cos φ0 / k) *
          (Real.sin ψ0 * Real.sin φ0) +
        (-Real.cos ψ0) * (-Real.cos ψ0) = 1
    calc
      _ = Real.sin ψ0 ^ 2 *
            (Real.sin φ0 ^ 2 + Real.cos φ0 ^ 2) +
          Real.cos ψ0 ^ 2 := by
            field_simp [hk] <;> ring
      _ = 1 := by
        rw [Real.sin_sq_add_cos_sq φ0]
        simpa using Real.sin_sq_add_cos_sq ψ0
  have hradMer :
      (Real.sin ψ0 * Real.cos φ0) ^ 2 +
          (Real.sin ψ0 * Real.sin φ0) ^ 2 +
          (-Real.cos ψ0) ^ 2 = 1 := by
    calc
      _ = Real.sin ψ0 ^ 2 *
            (Real.sin φ0 ^ 2 + Real.cos φ0 ^ 2) +
          Real.cos ψ0 ^ 2 := by ring
      _ = 1 := by
        rw [Real.sin_sq_add_cos_sq φ0]
        simpa using Real.sin_sq_add_cos_sq ψ0
  have hnormMer : norm3 (meridianDirection φ0 ψ0) = 1 := by
    change
      Real.sqrt
        ((Real.sin ψ0 * Real.cos φ0) ^ 2 +
          (Real.sin ψ0 * Real.sin φ0) ^ 2 +
          (-Real.cos ψ0) ^ 2) = 1
    rw [hradMer]
    exact Real.sqrt_one
  have hradCurve :
      (Real.sin ψ0 * Real.cos φ0 + Real.sin φ0 / k) ^ 2 +
          (Real.sin ψ0 * Real.sin φ0 - Real.cos φ0 / k) ^ 2 +
          (-Real.cos ψ0) ^ 2 = 1 + 1 / k ^ 2 := by
    calc
      _ = Real.sin ψ0 ^ 2 *
            (Real.sin φ0 ^ 2 + Real.cos φ0 ^ 2) +
          (Real.sin φ0 ^ 2 + Real.cos φ0 ^ 2) / k ^ 2 +
          Real.cos ψ0 ^ 2 := by
            field_simp [hk] <;> ring
      _ = (Real.sin ψ0 ^ 2 + Real.cos ψ0 ^ 2) + 1 / k ^ 2 := by
        rw [Real.sin_sq_add_cos_sq φ0]
        ring
      _ = 1 + 1 / k ^ 2 := by rw [Real.sin_sq_add_cos_sq ψ0]
  have hnormCurve :
      norm3 (curveDirection k (fun _ => φ0) ψ0) =
        Real.sqrt (1 + 1 / k ^ 2) := by
    change
      Real.sqrt
        ((Real.sin ψ0 * Real.cos φ0 + Real.sin φ0 / k) ^ 2 +
          (Real.sin ψ0 * Real.sin φ0 - Real.cos φ0 / k) ^ 2 +
          (-Real.cos ψ0) ^ 2) =
        Real.sqrt (1 + 1 / k ^ 2)
    exact congrArg Real.sqrt hradCurve
  rw [hdot, hnormCurve, hnormMer]
  ring

theorem gap15 (k φ0 ψ0 : ℝ) (hk : k ≠ 0) :
    angleCos k φ0 ψ0 = 1 / Real.sqrt (1 + 1 / k ^ 2) := by
  rw [gap13 k φ0 ψ0]
  exact gap14 k φ0 ψ0 hk

theorem gap16 (k φ0 ψ0 : ℝ) (hk : k ≠ 0) :
    angleCos k φ0 ψ0 = 1 / Real.sqrt (1 + 1 / k ^ 2) := by
  exact gap15 k φ0 ψ0 hk

end

end ProofGap.Exercise3536
