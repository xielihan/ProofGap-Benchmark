import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2050
noncomputable section

def denom (a b x : ℝ) := a * Real.sin x + b * Real.cos x
def numerator (a₁ b₁ c₁ x : ℝ) :=
  a₁ * Real.sin x ^ 2 + 2 * b₁ * Real.sin x * Real.cos x + c₁ * Real.cos x ^ 2
def coeffA (a b a₁ b₁ c₁ : ℝ) :=
  (b * c₁ - a₁ * b + 2 * a * b₁) / (a ^ 2 + b ^ 2)
def coeffB (a b a₁ b₁ c₁ : ℝ) :=
  (a * c₁ - a * a₁ - 2 * b * b₁) / (a ^ 2 + b ^ 2)
def coeffC (a b a₁ b₁ c₁ : ℝ) :=
  (a₁ * b ^ 2 + a ^ 2 * c₁ - 2 * a * b * b₁) / (a ^ 2 + b ^ 2)
def CoeffIdentity (a b a₁ b₁ c₁ A B C : ℝ) : Prop :=
  ∀ x, numerator a₁ b₁ c₁ x =
    (A * Real.cos x - B * Real.sin x) * denom a b x + C
def integrand (a b a₁ b₁ c₁ x : ℝ) := numerator a₁ b₁ c₁ x / denom a b x
def reciprocal (a b x : ℝ) := 1 / denom a b x
def explicitPart (a b a₁ b₁ c₁ x : ℝ) :=
  coeffA a b a₁ b₁ c₁ * Real.sin x + coeffB a b a₁ b₁ c₁ * Real.cos x
def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def LinearFamily (U : Set ℝ) (a b a₁ b₁ c₁ : ℝ) :=
  {F : ℝ → ℝ | ∃ P ∈ Family U Real.cos, ∃ Q ∈ Family U Real.sin,
    ∃ R ∈ Family U (reciprocal a b), ∃ C₀, ∀ x ∈ U,
      F x = coeffA a b a₁ b₁ c₁ * P x -
        coeffB a b a₁ b₁ c₁ * Q x + coeffC a b a₁ b₁ c₁ * R x + C₀}
def ReducedFamily (U : Set ℝ) (a b a₁ b₁ c₁ : ℝ) :=
  {F : ℝ → ℝ | ∃ R ∈ Family U (reciprocal a b), ∃ C₀,
    ∀ x ∈ U, F x = explicitPart a b a₁ b₁ c₁ x +
      coeffC a b a₁ b₁ c₁ * R x + C₀}
def Regular (U : Set ℝ) (a b : ℝ) : Prop :=
  IsOpen U ∧ IsPreconnected U ∧ ∀ x ∈ U, denom a b x ≠ 0

private theorem sumsq_pos {a b : ℝ} (hab : a ≠ 0 ∨ b ≠ 0) :
    0 < a ^ 2 + b ^ 2 := by
  rcases hab with ha | hb
  · have ha' : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    nlinarith [sq_nonneg b]
  · have hb' : 0 < b ^ 2 := sq_pos_of_ne_zero hb
    nlinarith [sq_nonneg a]

private def radius (a b : ℝ) : ℝ := Real.sqrt (a ^ 2 + b ^ 2)

private def conjugate (a b x : ℝ) : ℝ :=
  a * Real.cos x - b * Real.sin x

private def reciprocalPrimitive (a b : ℝ) (x : ℝ) : ℝ :=
  -(1 / radius a b) *
    (Real.log (radius a b + conjugate a b x) - Real.log (denom a b x))

private theorem radius_sq {a b : ℝ} (hab : a ≠ 0 ∨ b ≠ 0) :
    radius a b ^ 2 = a ^ 2 + b ^ 2 := by
  unfold radius
  exact Real.sq_sqrt (le_of_lt (sumsq_pos hab))

private theorem radius_ne_zero {a b : ℝ} (hab : a ≠ 0 ∨ b ≠ 0) :
    radius a b ≠ 0 :=
  ne_of_gt (by
    unfold radius
    exact Real.sqrt_pos.2 (sumsq_pos hab))

private theorem circle_identity (a b x : ℝ) :
    denom a b x ^ 2 + conjugate a b x ^ 2 = a ^ 2 + b ^ 2 := by
  calc
    denom a b x ^ 2 + conjugate a b x ^ 2 =
        (a ^ 2 + b ^ 2) * (Real.sin x ^ 2 + Real.cos x ^ 2) := by
          unfold denom conjugate
          ring
    _ = a ^ 2 + b ^ 2 := by
      rw [Real.sin_sq_add_cos_sq]
      ring

private theorem radius_add_conjugate_ne_zero {a b x : ℝ}
    (hab : a ≠ 0 ∨ b ≠ 0) (hd : denom a b x ≠ 0) :
    radius a b + conjugate a b x ≠ 0 := by
  intro hs
  have hq : conjugate a b x = -radius a b := by linarith
  have hc := circle_identity a b x
  have hr := radius_sq hab
  rw [hq] at hc
  have hd2 : denom a b x ^ 2 = 0 := by nlinarith
  have hd0 : denom a b x = 0 := by nlinarith
  exact hd hd0

private theorem reciprocalPrimitive_hasDerivAt {a b x : ℝ}
    (hab : a ≠ 0 ∨ b ≠ 0) (hd : denom a b x ≠ 0) :
    HasDerivAt (reciprocalPrimitive a b) (reciprocal a b x) x := by
  have hrne : radius a b ≠ 0 := radius_ne_zero hab
  have hsne : radius a b + conjugate a b x ≠ 0 :=
    radius_add_conjugate_ne_zero hab hd
  have hden : HasDerivAt (denom a b) (conjugate a b x) x := by
    convert ((Real.hasDerivAt_sin x).const_mul a).add
      ((Real.hasDerivAt_cos x).const_mul b) using 1 <;>
      simp [denom, conjugate, mul_neg] <;> ring
  have hconj : HasDerivAt (conjugate a b) (-denom a b x) x := by
    convert ((Real.hasDerivAt_cos x).const_mul a).sub
      ((Real.hasDerivAt_sin x).const_mul b) using 1 <;>
      simp [denom, conjugate, mul_neg] <;> ring
  have hsum : HasDerivAt
      (fun y => radius a b + conjugate a b y) (-denom a b x) x := by
    convert (hasDerivAt_const x (radius a b)).add hconj using 1 <;>
      simp only [Pi.add_apply, zero_add]
  have hlogsum := (Real.hasDerivAt_log hsne).comp x hsum
  have hlogden := (Real.hasDerivAt_log hd).comp x hden
  have hp := (hlogsum.sub hlogden).const_mul (-(1 / radius a b))
  unfold reciprocalPrimitive reciprocal
  convert hp using 1
  field_simp [hrne, hsne, hd] <;>
    nlinarith [circle_identity a b x, radius_sq hab]

private theorem explicitPart_hasDerivAt (a b a₁ b₁ c₁ x : ℝ) :
    HasDerivAt (explicitPart a b a₁ b₁ c₁)
      (coeffA a b a₁ b₁ c₁ * Real.cos x -
        coeffB a b a₁ b₁ c₁ * Real.sin x) x := by
  unfold explicitPart
  convert ((Real.hasDerivAt_sin x).const_mul (coeffA a b a₁ b₁ c₁)).add
    ((Real.hasDerivAt_cos x).const_mul (coeffB a b a₁ b₁ c₁)) using 1 <;>
    simp [mul_neg] <;> ring

private theorem primitive_eq_add_const
    (U : Set ℝ) (hopen : IsOpen U) (hconn : IsPreconnected U)
    (f g p : ℝ → ℝ)
    (hf : ∀ x ∈ U, HasDerivAt f (p x) x)
    (hg : ∀ x ∈ U, HasDerivAt g (p x) x) :
    ∃ C : ℝ, ∀ x ∈ U, f x = g x + C := by
  by_cases hne : U.Nonempty
  · rcases hne with ⟨x₀, hx₀⟩
    have hdiff : DifferentiableOn ℝ (fun y => f y - g y) U := by
      intro y hy
      exact ((hf y hy).sub (hg y hy)).differentiableAt.differentiableWithinAt
    have hzero : ∀ y ∈ U, deriv (fun z => f z - g z) y = 0 := by
      intro y hy
      simpa using ((hf y hy).sub (hg y hy)).deriv
    refine ⟨f x₀ - g x₀, ?_⟩
    intro x hx
    have heq : (fun y => f y - g y) x = (fun y => f y - g y) x₀ :=
      hopen.is_const_of_deriv_eq_zero hconn hdiff hzero hx hx₀
    dsimp at heq ⊢
    linarith
  · refine ⟨0, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

theorem gap1 (a b a₁ b₁ c₁ : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
    a * coeffA a b a₁ b₁ c₁ - b * coeffB a b a₁ b₁ c₁ = 2 * b₁ := by
  unfold coeffA coeffB
  field_simp [ne_of_gt (sumsq_pos hab)] <;> ring
theorem gap2 (a b a₁ b₁ c₁ : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
    coeffC a b a₁ b₁ c₁ - a * coeffB a b a₁ b₁ c₁ = a₁ := by
  unfold coeffB coeffC
  field_simp [ne_of_gt (sumsq_pos hab)] <;> ring
theorem gap3 (a b a₁ b₁ c₁ : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
    coeffC a b a₁ b₁ c₁ + b * coeffA a b a₁ b₁ c₁ = c₁ := by
  unfold coeffA coeffC
  field_simp [ne_of_gt (sumsq_pos hab)] <;> ring
theorem gap4 (a b a₁ b₁ c₁ : ℝ) :
    coeffA a b a₁ b₁ c₁ =
      (b * c₁ - a₁ * b + 2 * a * b₁) / (a ^ 2 + b ^ 2) := by
  rfl
theorem gap5 (a b a₁ b₁ c₁ : ℝ) :
    coeffB a b a₁ b₁ c₁ =
      (a * c₁ - a * a₁ - 2 * b * b₁) / (a ^ 2 + b ^ 2) := by
  rfl
theorem gap6 (a b a₁ b₁ c₁ : ℝ) :
    coeffC a b a₁ b₁ c₁ =
      (a₁ * b ^ 2 + a ^ 2 * c₁ - 2 * a * b * b₁) / (a ^ 2 + b ^ 2) := by
  rfl
theorem gap7 (U : Set ℝ) (a b a₁ b₁ c₁ : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (hU : Regular U a b) :
    Family U (integrand a b a₁ b₁ c₁) = LinearFamily U a b a₁ b₁ c₁ := by
  rcases hU with ⟨hopen, hconn, hreg⟩
  let A := coeffA a b a₁ b₁ c₁
  let B := coeffB a b a₁ b₁ c₁
  let C := coeffC a b a₁ b₁ c₁
  have hcoeff : CoeffIdentity a b a₁ b₁ c₁ A B C := by
    intro x
    unfold numerator denom
    calc
      a₁ * Real.sin x ^ 2 + 2 * b₁ * Real.sin x * Real.cos x +
          c₁ * Real.cos x ^ 2 =
          (C - a * B) * Real.sin x ^ 2 +
            (a * A - b * B) * Real.sin x * Real.cos x +
            (C + b * A) * Real.cos x ^ 2 := by
              rw [gap1 a b a₁ b₁ c₁ hab, gap2 a b a₁ b₁ c₁ hab,
                gap3 a b a₁ b₁ c₁ hab]
      _ = (A * Real.cos x - B * Real.sin x) *
            (a * Real.sin x + b * Real.cos x) +
            C * (Real.sin x ^ 2 + Real.cos x ^ 2) := by ring
      _ = (A * Real.cos x - B * Real.sin x) *
            (a * Real.sin x + b * Real.cos x) + C := by
              rw [Real.sin_sq_add_cos_sq]
              ring
  have hdecomp : ∀ x ∈ U,
      integrand a b a₁ b₁ c₁ x =
        A * Real.cos x - B * Real.sin x + C * reciprocal a b x := by
    intro x hx
    unfold integrand reciprocal
    rw [hcoeff x]
    field_simp [hreg x hx] <;> ring
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ U, HasDerivAt F (integrand a b a₁ b₁ c₁ x) x at hF
    let R₀ := reciprocalPrimitive a b
    have hR₀ : R₀ ∈ Family U (reciprocal a b) := by
      change ∀ x ∈ U, HasDerivAt R₀ (reciprocal a b x) x
      intro x hx
      exact reciprocalPrimitive_hasDerivAt hab (hreg x hx)
    let G : ℝ → ℝ := fun x => explicitPart a b a₁ b₁ c₁ x + C * R₀ x
    have hG : ∀ x ∈ U, HasDerivAt G (integrand a b a₁ b₁ c₁ x) x := by
      intro x hx
      have hRx : HasDerivAt R₀ (reciprocal a b x) x := hR₀ x hx
      have hd := (explicitPart_hasDerivAt a b a₁ b₁ c₁ x).add
        (hRx.const_mul C)
      simpa [G, hdecomp x hx] using hd
    obtain ⟨C₀, hFG⟩ :=
      primitive_eq_add_const U hopen hconn F G
        (integrand a b a₁ b₁ c₁) hF hG
    change ∃ P ∈ Family U Real.cos, ∃ Q ∈ Family U Real.sin,
      ∃ R ∈ Family U (reciprocal a b), ∃ C₀, ∀ x ∈ U,
        F x = A * P x - B * Q x + C * R x + C₀
    refine ⟨Real.sin, ?_, fun x => -Real.cos x, ?_, R₀, hR₀, C₀, ?_⟩
    · change ∀ x ∈ U, HasDerivAt Real.sin (Real.cos x) x
      intro x hx
      exact Real.hasDerivAt_sin x
    · change ∀ x ∈ U, HasDerivAt (fun x => -Real.cos x) (Real.sin x) x
      intro x hx
      simpa using (Real.hasDerivAt_cos x).neg
    · intro x hx
      rw [hFG x hx]
      simp [G, explicitPart]
      ring
  · intro hLin
    change ∃ P ∈ Family U Real.cos, ∃ Q ∈ Family U Real.sin,
      ∃ R ∈ Family U (reciprocal a b), ∃ C₀, ∀ x ∈ U,
        F x = A * P x - B * Q x + C * R x + C₀ at hLin
    rcases hLin with ⟨P, hP, Q, hQ, R, hR, C₀, hrep⟩
    change ∀ x ∈ U, HasDerivAt F (integrand a b a₁ b₁ c₁ x) x
    intro x hx
    let H : ℝ → ℝ := fun y => A * P y - B * Q y + C * R y + C₀
    have hd : HasDerivAt H (integrand a b a₁ b₁ c₁ x) x := by
      have hd₀ := ((((hP x hx).const_mul A).sub
        ((hQ x hx).const_mul B)).add ((hR x hx).const_mul C)).add_const C₀
      dsimp [H]
      simpa [hdecomp x hx] using hd₀
    have heq : F =ᶠ[nhds x] H := by
      exact Filter.mem_of_superset (hopen.mem_nhds hx) (fun y hy => by
        dsimp [H]
        exact hrep y hy)
    exact hd.congr_of_eventuallyEq heq
theorem gap8 (U : Set ℝ) (a b a₁ b₁ c₁ : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (hU : Regular U a b) :
    LinearFamily U a b a₁ b₁ c₁ = ReducedFamily U a b a₁ b₁ c₁ := by
  rcases hU with ⟨hopen, hconn, hreg⟩
  let A := coeffA a b a₁ b₁ c₁
  let B := coeffB a b a₁ b₁ c₁
  let C := coeffC a b a₁ b₁ c₁
  apply Set.ext
  intro F
  constructor
  · intro hLin
    change ∃ P ∈ Family U Real.cos, ∃ Q ∈ Family U Real.sin,
      ∃ R ∈ Family U (reciprocal a b), ∃ C₀, ∀ x ∈ U,
        F x = A * P x - B * Q x + C * R x + C₀ at hLin
    rcases hLin with ⟨P, hP, Q, hQ, R, hR, C₀, hrep⟩
    let H : ℝ → ℝ := fun x => A * P x - B * Q x
    have hH : ∀ x ∈ U,
        HasDerivAt H (A * Real.cos x - B * Real.sin x) x := by
      intro x hx
      dsimp [H]
      simpa using ((hP x hx).const_mul A).sub ((hQ x hx).const_mul B)
    have hE : ∀ x ∈ U,
        HasDerivAt (explicitPart a b a₁ b₁ c₁)
          (A * Real.cos x - B * Real.sin x) x := by
      intro x hx
      exact explicitPart_hasDerivAt a b a₁ b₁ c₁ x
    obtain ⟨K, hK⟩ := primitive_eq_add_const U hopen hconn H
      (explicitPart a b a₁ b₁ c₁)
      (fun x => A * Real.cos x - B * Real.sin x) hH hE
    change ∃ R ∈ Family U (reciprocal a b), ∃ C₀, ∀ x ∈ U,
      F x = explicitPart a b a₁ b₁ c₁ x + C * R x + C₀
    refine ⟨R, hR, K + C₀, ?_⟩
    intro x hx
    have hKx : A * P x - B * Q x =
        explicitPart a b a₁ b₁ c₁ x + K := by
      simpa [H] using hK x hx
    rw [hrep x hx, hKx]
    ring
  · intro hRed
    change ∃ R ∈ Family U (reciprocal a b), ∃ C₀, ∀ x ∈ U,
      F x = explicitPart a b a₁ b₁ c₁ x + C * R x + C₀ at hRed
    rcases hRed with ⟨R, hR, C₀, hrep⟩
    change ∃ P ∈ Family U Real.cos, ∃ Q ∈ Family U Real.sin,
      ∃ R ∈ Family U (reciprocal a b), ∃ C₀, ∀ x ∈ U,
        F x = A * P x - B * Q x + C * R x + C₀
    refine ⟨Real.sin, ?_, fun x => -Real.cos x, ?_, R, hR, C₀, ?_⟩
    · change ∀ x ∈ U, HasDerivAt Real.sin (Real.cos x) x
      intro x hx
      exact Real.hasDerivAt_sin x
    · change ∀ x ∈ U, HasDerivAt (fun x => -Real.cos x) (Real.sin x) x
      intro x hx
      simpa using (Real.hasDerivAt_cos x).neg
    · intro x hx
      simpa [explicitPart] using hrep x hx
theorem gap9 (U : Set ℝ) (a b a₁ b₁ c₁ : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (hU : Regular U a b) :
    Family U (integrand a b a₁ b₁ c₁) = ReducedFamily U a b a₁ b₁ c₁ := by
  exact (gap7 U a b a₁ b₁ c₁ hab hU).trans
    (gap8 U a b a₁ b₁ c₁ hab hU)

end
end ProofGap.Exercise2050
