import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1829

noncomputable section

def branch : Set ℝ := Set.univ
def sinIntegrand (a b x : ℝ) := Real.exp (a * x) * Real.sin (b * x)
def cosIntegrand (a b x : ℝ) := Real.exp (a * x) * Real.cos (b * x)
def expSinChain (a b x : ℝ) :=
  Real.sin (b * x) * deriv (fun t : ℝ => Real.exp (a * t)) x
def expCosChain (a b x : ℝ) :=
  Real.cos (b * x) * deriv (fun t : ℝ => Real.exp (a * t)) x
def boundary₁ (a b x : ℝ) :=
  (1 / a) * Real.exp (a * x) * Real.sin (b * x)
def boundary₂ (a b x : ℝ) :=
  boundary₁ a b x - b / a ^ 2 * Real.exp (a * x) * Real.cos (b * x)
def primitive (a b x : ℝ) :=
  Real.exp (a * x) * (a * Real.sin (b * x) - b * Real.cos (b * x)) /
    (a ^ 2 + b ^ 2)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}
def ScaledFamily (c : ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn f, ∀ x ∈ branch, F x = c * G x}
def ByPartsFamily (a b : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (cosIntegrand a b),
    ∀ x ∈ branch, F x = boundary₁ a b x - b / a * G x}
def SecondChainFamily (a b : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (expCosChain a b),
    ∀ x ∈ branch, F x = boundary₁ a b x - b / a ^ 2 * G x}
def RecurrenceFamily (a b : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (sinIntegrand a b),
    ∀ x ∈ branch, F x = boundary₂ a b x - b ^ 2 / a ^ 2 * G x}

private theorem hasDerivAt_exp_mul (a x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (a * t))
      (a * Real.exp (a * x)) x := by
  convert (Real.hasDerivAt_exp (a * x)).comp x
      ((hasDerivAt_id x).const_mul a) using 1 <;> ring

private theorem hasDerivAt_sin_mul (b x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (b * t))
      (b * Real.cos (b * x)) x := by
  convert (Real.hasDerivAt_sin (b * x)).comp x
      ((hasDerivAt_id x).const_mul b) using 1 <;> ring

private theorem hasDerivAt_cos_mul (b x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cos (b * t))
      (-b * Real.sin (b * x)) x := by
  convert (Real.hasDerivAt_cos (b * x)).comp x
      ((hasDerivAt_id x).const_mul b) using 1 <;> ring

private theorem expSinChain_eq (a b x : ℝ) :
    expSinChain a b x = a * sinIntegrand a b x := by
  unfold expSinChain sinIntegrand
  rw [(hasDerivAt_exp_mul a x).deriv]
  ring

private theorem expCosChain_eq (a b x : ℝ) :
    expCosChain a b x = a * cosIntegrand a b x := by
  unfold expCosChain cosIntegrand
  rw [(hasDerivAt_exp_mul a x).deriv]
  ring

private theorem antiderivatives_eq_primitive_of_hasDerivAt
    (f p : ℝ → ℝ) (hp : ∀ x, HasDerivAt p (f x) x) :
    AntiderivativesOn f = PrimitiveFamily p := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (f x) x) ↔
      ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C
  constructor
  · intro hF
    let q : ℝ → ℝ := fun t => F t - p t
    have hd : ∀ x, HasDerivAt q 0 x := by
      intro x
      dsimp [q]
      convert (hF x (by simp [branch])).sub (hp x) using 1 <;> ring
    have hdiff : Differentiable ℝ q := by
      intro x
      exact (hd x).differentiableAt
    have hderiv : ∀ x : ℝ, deriv q x = 0 := by
      intro x
      exact (hd x).deriv
    refine ⟨F 0 - p 0, ?_⟩
    intro x hx
    have hc : q x = q (0 : ℝ) :=
      is_const_of_deriv_eq_zero hdiff hderiv x (0 : ℝ)
    dsimp [q] at hc
    linarith
  · rintro ⟨C, hC⟩
    have hfun : F = fun x => p x + C := by
      funext x
      exact hC x (by simp [branch])
    intro x hx
    rw [hfun]
    simpa using (hp x).const_add C

private theorem hasDerivAt_primitive (a b : ℝ) (ha : a ≠ 0) (x : ℝ) :
    HasDerivAt (primitive a b) (sinIntegrand a b x) x := by
  have hden : a ^ 2 + b ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
  have hq := ((hasDerivAt_sin_mul b x).const_mul a).sub
    ((hasDerivAt_cos_mul b x).const_mul b)
  have hprod := (hasDerivAt_exp_mul a x).mul hq
  change HasDerivAt
    (fun t : ℝ =>
      Real.exp (a * t) *
          (a * Real.sin (b * t) - b * Real.cos (b * t)) /
        (a ^ 2 + b ^ 2))
    (sinIntegrand a b x) x
  convert hprod.div_const (a ^ 2 + b ^ 2) using 1
  unfold sinIntegrand
  simp only [Pi.sub_apply]
  field_simp [hden]
  ring

private theorem boundary₁_hasDerivAt (a b : ℝ) (ha : a ≠ 0) (x : ℝ) :
    HasDerivAt (boundary₁ a b)
      (sinIntegrand a b x + b / a * cosIntegrand a b x) x := by
  have hd :=
    ((hasDerivAt_exp_mul a x).mul (hasDerivAt_sin_mul b x)).const_mul
      (1 / a)
  convert hd using 1
  · funext y
    simp [boundary₁]
    ring
  · unfold sinIntegrand cosIntegrand
    field_simp [ha]

private theorem boundary₂_hasDerivAt (a b : ℝ) (ha : a ≠ 0) (x : ℝ) :
    HasDerivAt (boundary₂ a b)
      ((1 + b ^ 2 / a ^ 2) * sinIntegrand a b x) x := by
  have hsecond :=
    ((hasDerivAt_exp_mul a x).mul (hasDerivAt_cos_mul b x)).const_mul
      (b / a ^ 2)
  have hsecond' :
      HasDerivAt
        (fun t : ℝ =>
          b / a ^ 2 * Real.exp (a * t) * Real.cos (b * t))
        (b / a ^ 2 *
          (a * Real.exp (a * x) * Real.cos (b * x) +
            Real.exp (a * x) * (-b * Real.sin (b * x)))) x := by
    convert hsecond using 1
    funext y
    simp
    ring
  have hd := (boundary₁_hasDerivAt a b ha x).sub hsecond'
  convert hd using 1
  · unfold sinIntegrand cosIntegrand
    field_simp [ha]
    ring

private theorem antiderivatives_eq_byParts (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    AntiderivativesOn (sinIntegrand a b) = ByPartsFamily a b := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (sinIntegrand a b x) x at hF
    change ∃ G ∈ AntiderivativesOn (cosIntegrand a b),
      ∀ x ∈ branch, F x = boundary₁ a b x - b / a * G x
    refine ⟨fun x => (a / b) * (boundary₁ a b x - F x), ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun x => (a / b) * (boundary₁ a b x - F x))
          (cosIntegrand a b x) x
      intro x hx
      have hd :=
        ((boundary₁_hasDerivAt a b ha x).sub (hF x hx)).const_mul
          (a / b)
      convert hd using 1 <;> field_simp [ha, hb] <;> ring
    · intro x hx
      field_simp [ha, hb]
      ring
  · rintro ⟨G, hG, hFG⟩
    change ∀ x ∈ branch, HasDerivAt F (sinIntegrand a b x) x
    have hfun : F = fun x => boundary₁ a b x - b / a * G x := by
      funext x
      exact hFG x (by simp [branch])
    rw [hfun]
    intro x hx
    have hd :=
      (boundary₁_hasDerivAt a b ha x).sub
        ((hG x hx).const_mul (b / a))
    convert hd using 1 <;> field_simp [ha] <;> ring

private theorem antiderivatives_eq_recurrence (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    AntiderivativesOn (sinIntegrand a b) = RecurrenceFamily a b := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (sinIntegrand a b x) x at hF
    change ∃ G ∈ AntiderivativesOn (sinIntegrand a b),
      ∀ x ∈ branch, F x = boundary₂ a b x - b ^ 2 / a ^ 2 * G x
    refine ⟨fun x => (a ^ 2 / b ^ 2) * (boundary₂ a b x - F x), ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt
          (fun x => (a ^ 2 / b ^ 2) * (boundary₂ a b x - F x))
          (sinIntegrand a b x) x
      intro x hx
      have hd :=
        ((boundary₂_hasDerivAt a b ha x).sub (hF x hx)).const_mul
          (a ^ 2 / b ^ 2)
      convert hd using 1 <;> field_simp [ha, hb] <;> ring
    · intro x hx
      field_simp [ha, hb]
      ring
  · rintro ⟨G, hG, hFG⟩
    change ∀ x ∈ branch, HasDerivAt F (sinIntegrand a b x) x
    have hfun : F =
        fun x => boundary₂ a b x - b ^ 2 / a ^ 2 * G x := by
      funext x
      exact hFG x (by simp [branch])
    rw [hfun]
    intro x hx
    have hd :=
      (boundary₂_hasDerivAt a b ha x).sub
        ((hG x hx).const_mul (b ^ 2 / a ^ 2))
    convert hd using 1 <;> field_simp [ha] <;> ring

theorem gap1 (a b : ℝ) (ha : a = 0) (hb : b = 0) :
    AntiderivativesOn (sinIntegrand a b) =
      PrimitiveFamily (fun _ => 0) := by
  apply antiderivatives_eq_primitive_of_hasDerivAt
  intro x
  simpa [sinIntegrand, ha, hb] using (hasDerivAt_const x (0 : ℝ))
theorem gap2 (a b : ℝ) (ha : a = 0) (hb : b ≠ 0) :
    AntiderivativesOn (sinIntegrand a b) =
      PrimitiveFamily (fun x => -(1 / b) * Real.cos (b * x)) := by
  subst a
  apply antiderivatives_eq_primitive_of_hasDerivAt
  intro x
  have h := (hasDerivAt_cos_mul b x).const_mul (-(1 / b))
  convert h using 1
  simp only [sinIntegrand, zero_mul, Real.exp_zero, one_mul]
  field_simp [hb] <;> ring
theorem gap3 (a b : ℝ) (ha : a ≠ 0) :
    AntiderivativesOn (sinIntegrand a b) =
      ScaledFamily (1 / a) (expSinChain a b) := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (sinIntegrand a b x) x) ↔
      ∃ G, (∀ x ∈ branch, HasDerivAt G (expSinChain a b x) x) ∧
        ∀ x ∈ branch, F x = (1 / a) * G x
  constructor
  · intro hF
    refine ⟨fun x => a * F x, ?_, ?_⟩
    · intro x hx
      simpa only [expSinChain_eq] using (hF x hx).const_mul a
    · intro x hx
      field_simp [ha]
  · rintro ⟨G, hG, hFG⟩
    have hfun : F = fun x => (1 / a) * G x := by
      funext x
      exact hFG x (by simp [branch])
    intro x hx
    rw [hfun]
    have hd := (hG x hx).const_mul (1 / a)
    rw [expSinChain_eq] at hd
    convert hd using 1
    field_simp [ha]
theorem gap4 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ScaledFamily (1 / a) (expSinChain a b) =
      ByPartsFamily a b := by
  calc
    ScaledFamily (1 / a) (expSinChain a b) =
        AntiderivativesOn (sinIntegrand a b) := (gap3 a b ha).symm
    _ = ByPartsFamily a b := antiderivatives_eq_byParts a b ha hb
theorem gap5 (a b : ℝ) (ha : a ≠ 0) :
    ByPartsFamily a b = SecondChainFamily a b := by
  apply Set.ext
  intro F
  change
    (∃ G, (∀ x ∈ branch, HasDerivAt G (cosIntegrand a b x) x) ∧
        ∀ x ∈ branch, F x = boundary₁ a b x - b / a * G x) ↔
      ∃ H, (∀ x ∈ branch, HasDerivAt H (expCosChain a b x) x) ∧
        ∀ x ∈ branch, F x = boundary₁ a b x - b / a ^ 2 * H x
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨fun x => a * G x, ?_, ?_⟩
    · intro x hx
      simpa only [expCosChain_eq] using (hG x hx).const_mul a
    · intro x hx
      rw [hFG x hx]
      field_simp [ha]
  · rintro ⟨H, hH, hFH⟩
    refine ⟨fun x => (1 / a) * H x, ?_, ?_⟩
    · intro x hx
      have hd := (hH x hx).const_mul (1 / a)
      rw [expCosChain_eq] at hd
      convert hd using 1
      field_simp [ha]
    · intro x hx
      rw [hFH x hx]
      field_simp [ha]
theorem gap6 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    AntiderivativesOn (sinIntegrand a b) =
      SecondChainFamily a b := by
  calc
    AntiderivativesOn (sinIntegrand a b) =
        ScaledFamily (1 / a) (expSinChain a b) := gap3 a b ha
    _ = ByPartsFamily a b := gap4 a b ha hb
    _ = SecondChainFamily a b := gap5 a b ha
theorem gap7 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    AntiderivativesOn (sinIntegrand a b) =
      RecurrenceFamily a b := by
  exact antiderivatives_eq_recurrence a b ha hb
theorem gap8 (a b : ℝ) (ha : a ≠ 0) :
    AntiderivativesOn (sinIntegrand a b) =
      PrimitiveFamily (primitive a b) := by
  apply antiderivatives_eq_primitive_of_hasDerivAt
  intro x
  exact hasDerivAt_primitive a b ha x

end
end ProofGap.Exercise1829
