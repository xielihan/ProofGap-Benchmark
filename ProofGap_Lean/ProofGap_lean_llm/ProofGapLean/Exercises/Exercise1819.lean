import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1819

noncomputable section

def branch : Set ℝ := Set.univ
def integrand (a x : ℝ) := Real.sqrt (x ^ 2 + a)
def residual₁ (a x : ℝ) := x ^ 2 / Real.sqrt (x ^ 2 + a)
def reciprocalSqrt (a x : ℝ) := 1 / Real.sqrt (x ^ 2 + a)
def boundary₁ (a x : ℝ) := x * Real.sqrt (x ^ 2 + a)
def boundary₂ (a x : ℝ) := x / 2 * Real.sqrt (x ^ 2 + a)
def primitive (a x : ℝ) :=
  boundary₂ a x +
    a / 2 * Real.log |x + Real.sqrt (x ^ 2 + a)|
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def FirstByPartsFamily (a : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (residual₁ a),
    ∀ x ∈ branch, F x = boundary₁ a x - G x}
def SplitFamily (a : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (integrand a),
    ∃ H ∈ AntiderivativesOn (reciprocalSqrt a),
      ∀ x ∈ branch, F x = boundary₁ a x - G x + a * H x}
def SecondByPartsFamily (a : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (reciprocalSqrt a),
    ∀ x ∈ branch, F x = boundary₂ a x + a / 2 * G x}
def PrimitiveFamily (a : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive a x + C}

private theorem hasDerivAt_sqrt_quadratic (a : ℝ) (ha : 0 < a) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 + a))
      (x / Real.sqrt (x ^ 2 + a)) x := by
  have hq : 0 < x ^ 2 + a := by
    nlinarith [sq_nonneg x]
  have hs : 0 < Real.sqrt (x ^ 2 + a) := Real.sqrt_pos.2 hq
  have hi : HasDerivAt (fun y : ℝ => y ^ 2 + a) (2 * x) x := by
    simpa [add_comm] using ((hasDerivAt_id x).pow 2).add_const a
  have h := (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hi
  convert h using 1
  field_simp [ne_of_gt hs]
  <;> ring

private theorem hasDerivAt_boundary₁ (a : ℝ) (ha : 0 < a) (x : ℝ) :
    HasDerivAt (boundary₁ a)
      (integrand a x + residual₁ a x) x := by
  have hs := hasDerivAt_sqrt_quadratic a ha x
  unfold boundary₁ integrand residual₁
  convert (hasDerivAt_id x).mul hs using 1 <;>
    simp only [id_eq] <;> ring

private theorem hasDerivAt_boundary₂ (a : ℝ) (ha : 0 < a) (x : ℝ) :
    HasDerivAt (boundary₂ a)
      ((integrand a x + residual₁ a x) / 2) x := by
  have hs := hasDerivAt_sqrt_quadratic a ha x
  unfold boundary₂ integrand residual₁
  convert ((hasDerivAt_id x).div_const 2).mul hs using 1 <;>
    simp only [id_eq] <;> ring

private theorem hasDerivAt_reciprocalPrimitive (a : ℝ) (ha : 0 < a) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.log |y + Real.sqrt (y ^ 2 + a)|)
      (reciprocalSqrt a x) x := by
  have hpos : ∀ y : ℝ, 0 < y + Real.sqrt (y ^ 2 + a) := by
    intro y
    have hq : 0 < y ^ 2 + a := by
      nlinarith [sq_nonneg y]
    have hs : 0 < Real.sqrt (y ^ 2 + a) := Real.sqrt_pos.2 hq
    have hsq := Real.sq_sqrt (le_of_lt hq)
    nlinarith
  have hsx : 0 < Real.sqrt (x ^ 2 + a) := by
    apply Real.sqrt_pos.2
    nlinarith [sq_nonneg x]
  have hs := hasDerivAt_sqrt_quadratic a ha x
  have hadd := (hasDerivAt_id x).add hs
  have hlog := (Real.hasDerivAt_log (ne_of_gt (hpos x))).comp x hadd
  have habs :
      (fun y : ℝ => Real.log |y + Real.sqrt (y ^ 2 + a)|) =
        fun y : ℝ => Real.log (y + Real.sqrt (y ^ 2 + a)) := by
    funext y
    rw [abs_of_pos (hpos y)]
  rw [habs]
  unfold reciprocalSqrt
  convert hlog using 1
  field_simp [ne_of_gt hsx, ne_of_gt (hpos x)]
  <;> ring

private theorem integrand_eq_residual_add (a : ℝ) (ha : 0 < a) (x : ℝ) :
    integrand a x = residual₁ a x + a * reciprocalSqrt a x := by
  have hq : 0 < x ^ 2 + a := by
    nlinarith [sq_nonneg x]
  have hs : 0 < Real.sqrt (x ^ 2 + a) := Real.sqrt_pos.2 hq
  have hsq := Real.sq_sqrt (le_of_lt hq)
  unfold integrand residual₁ reciprocalSqrt
  field_simp [ne_of_gt hs] <;> nlinarith [hsq]

private theorem functions_eq_add_const
    (f g : ℝ → ℝ) (d : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (d x) x)
    (hg : ∀ x, HasDerivAt g (d x) x) :
    ∃ C : ℝ, ∀ x, f x = g x + C := by
  let h : ℝ → ℝ := fun x => f x - g x
  have hz : ∀ x, HasDerivAt h 0 x := by
    intro x
    dsimp [h]
    convert (hf x).sub (hg x) using 1 <;> ring
  have hdiff : Differentiable ℝ h := fun x => (hz x).differentiableAt
  have hderiv : ∀ x, deriv h x = 0 := fun x => (hz x).deriv
  refine ⟨h 0, ?_⟩
  intro x
  have hc : h x = h 0 :=
    is_const_of_deriv_eq_zero hdiff hderiv x 0
  dsimp [h] at hc ⊢
  linarith

theorem gap1 (a : ℝ) (ha : 0 < a) :
    AntiderivativesOn (integrand a) = FirstByPartsFamily a := by
  ext F
  simp only [AntiderivativesOn, FirstByPartsFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun x => boundary₁ a x - F x, ?_, ?_⟩
    · intro x hx
      have hd := (hasDerivAt_boundary₁ a ha x).sub (hF x hx)
      convert hd using 1 <;> ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    have hfun : F = fun y => boundary₁ a y - G y := by
      funext y
      exact hFG y (by simp [branch])
    rw [hfun]
    intro x hx
    have hd := (hasDerivAt_boundary₁ a ha x).sub (hG x hx)
    convert hd using 1 <;> ring
theorem gap2 (a : ℝ) (ha : 0 < a) :
    FirstByPartsFamily a = SplitFamily a := by
  ext F
  simp only [FirstByPartsFamily, SplitFamily, AntiderivativesOn,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, hG, hFG⟩
    let H : ℝ → ℝ := fun y => Real.log |y + Real.sqrt (y ^ 2 + a)|
    let I : ℝ → ℝ := fun y => G y + a * H y
    refine ⟨I, ?_, H, ?_, ?_⟩
    · intro x hx
      have hd := (hG x hx).add ((hasDerivAt_reciprocalPrimitive a ha x).const_mul a)
      convert hd using 1
      rw [integrand_eq_residual_add a ha x]
    · intro x hx
      exact hasDerivAt_reciprocalPrimitive a ha x
    · intro x hx
      dsimp [I, H]
      rw [hFG x hx]
      ring
  · rintro ⟨I, hI, H, hH, hFIH⟩
    refine ⟨fun y => I y - a * H y, ?_, ?_⟩
    · intro x hx
      have hd := (hI x hx).sub ((hH x hx).const_mul a)
      convert hd using 1
      rw [integrand_eq_residual_add a ha x]
      ring
    · intro x hx
      rw [hFIH x hx]
      ring
theorem gap3 (a : ℝ) (ha : 0 < a) :
    AntiderivativesOn (integrand a) = SplitFamily a := by
  exact (gap1 a ha).trans (gap2 a ha)
theorem gap4 (a : ℝ) (ha : 0 < a) :
    AntiderivativesOn (integrand a) = SecondByPartsFamily a := by
  ext F
  simp only [AntiderivativesOn, SecondByPartsFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    let G : ℝ → ℝ := fun y => (2 / a) * (F y - boundary₂ a y)
    refine ⟨G, ?_, ?_⟩
    · intro x hx
      have hd := ((hF x hx).sub (hasDerivAt_boundary₂ a ha x)).const_mul (2 / a)
      convert hd using 1
      rw [integrand_eq_residual_add a ha x]
      field_simp [ne_of_gt ha]
      ring
    · intro x hx
      dsimp [G]
      field_simp [ne_of_gt ha]
      ring
  · rintro ⟨G, hG, hFG⟩
    have hfun : F = fun y => boundary₂ a y + a / 2 * G y := by
      funext y
      exact hFG y (by simp [branch])
    rw [hfun]
    intro x hx
    have hd := (hasDerivAt_boundary₂ a ha x).add ((hG x hx).const_mul (a / 2))
    convert hd using 1
    rw [integrand_eq_residual_add a ha x]
    ring
theorem gap5 (a : ℝ) (ha : 0 < a) :
    SecondByPartsFamily a = PrimitiveFamily a := by
  ext F
  simp only [SecondByPartsFamily, PrimitiveFamily, AntiderivativesOn,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, hG, hFG⟩
    let H : ℝ → ℝ := fun y => Real.log |y + Real.sqrt (y ^ 2 + a)|
    have hGall : ∀ x, HasDerivAt G (reciprocalSqrt a x) x := by
      intro x
      exact hG x (by simp [branch])
    have hHall : ∀ x, HasDerivAt H (reciprocalSqrt a x) x := by
      intro x
      exact hasDerivAt_reciprocalPrimitive a ha x
    obtain ⟨C, hC⟩ := functions_eq_add_const G H (reciprocalSqrt a) hGall hHall
    refine ⟨a / 2 * C, ?_⟩
    intro x hx
    rw [hFG x hx, hC x]
    unfold primitive
    dsimp [H]
    ring
  · rintro ⟨C, hFC⟩
    let H : ℝ → ℝ := fun y => Real.log |y + Real.sqrt (y ^ 2 + a)|
    let G : ℝ → ℝ := fun y => H y + 2 / a * C
    refine ⟨G, ?_, ?_⟩
    · intro x hx
      simpa [G, H] using
        (hasDerivAt_reciprocalPrimitive a ha x).add_const (2 / a * C)
    · intro x hx
      rw [hFC x hx]
      unfold primitive
      dsimp [G, H]
      field_simp [ne_of_gt ha]
      ring
theorem gap6 (a : ℝ) (ha : 0 < a) :
    AntiderivativesOn (integrand a) = PrimitiveFamily a := by
  exact (gap4 a ha).trans (gap5 a ha)

end
end ProofGap.Exercise1819
