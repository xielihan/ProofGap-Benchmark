import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1828

noncomputable section

def branch : Set ℝ := Set.univ
def cosIntegrand (a b x : ℝ) := Real.exp (a * x) * Real.cos (b * x)
def sinIntegrand (a b x : ℝ) := Real.exp (a * x) * Real.sin (b * x)
def expCosChain (a b x : ℝ) :=
  Real.cos (b * x) * deriv (fun t : ℝ => Real.exp (a * t)) x
def expSinChain (a b x : ℝ) :=
  Real.sin (b * x) * deriv (fun t : ℝ => Real.exp (a * t)) x
def boundary₁ (a b x : ℝ) :=
  (1 / a) * Real.exp (a * x) * Real.cos (b * x)
def boundary₂ (a b x : ℝ) :=
  boundary₁ a b x + b / a ^ 2 * Real.exp (a * x) * Real.sin (b * x)
def primitiveRaw (a b x : ℝ) :=
  a ^ 2 / (a ^ 2 + b ^ 2) *
    ((1 / a) * Real.exp (a * x) * Real.cos (b * x) +
      b / a ^ 2 * Real.exp (a * x) * Real.sin (b * x))
def primitive (a b x : ℝ) :=
  Real.exp (a * x) * (a * Real.cos (b * x) + b * Real.sin (b * x)) /
    (a ^ 2 + b ^ 2)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}
def ScaledFamily (c : ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn f, ∀ x ∈ branch, F x = c * G x}
def ByPartsFamily (a b : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (sinIntegrand a b),
    ∀ x ∈ branch, F x = boundary₁ a b x + b / a * G x}
def SecondChainFamily (a b : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (expSinChain a b),
    ∀ x ∈ branch, F x = boundary₁ a b x + b / a ^ 2 * G x}
def RecurrenceFamily (a b : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn (cosIntegrand a b),
    ∀ x ∈ branch, F x = boundary₂ a b x - b ^ 2 / a ^ 2 * G x}

private theorem sum_sq_ne_zero_left {a b : ℝ} (ha : a ≠ 0) :
    a ^ 2 + b ^ 2 ≠ 0 := by
  intro h
  have ha_sq : a ^ 2 = 0 := by
    nlinarith [sq_nonneg a, sq_nonneg b]
  exact (pow_ne_zero 2 ha) ha_sq

private theorem hasDerivAt_exp_mul (a x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (a * t))
      (a * Real.exp (a * x)) x := by
  have harg : HasDerivAt (fun t : ℝ => a * t) a x := by
    simpa using (hasDerivAt_id x).const_mul a
  convert (Real.hasDerivAt_exp (a * x)).comp x harg using 1 <;> ring

private theorem expCosChain_eq (a b x : ℝ) :
    expCosChain a b x = a * cosIntegrand a b x := by
  have he := hasDerivAt_exp_mul a x
  unfold expCosChain cosIntegrand
  rw [he.deriv]
  ring

private theorem expSinChain_eq (a b x : ℝ) :
    expSinChain a b x = a * sinIntegrand a b x := by
  have he := hasDerivAt_exp_mul a x
  unfold expSinChain sinIntegrand
  rw [he.deriv]
  ring

private theorem primitive_hasDerivAt (a b : ℝ) (ha : a ≠ 0) (x : ℝ) :
    HasDerivAt (primitive a b) (cosIntegrand a b x) x := by
  have hden : a ^ 2 + b ^ 2 ≠ 0 := sum_sq_ne_zero_left ha
  have he := hasDerivAt_exp_mul a x
  have harg : HasDerivAt (fun t : ℝ => b * t) b x := by
    simpa using (hasDerivAt_id x).const_mul b
  have hc : HasDerivAt (fun t : ℝ => Real.cos (b * t))
      (-b * Real.sin (b * x)) x := by
    convert (Real.hasDerivAt_cos (b * x)).comp x harg using 1 <;> ring
  have hs : HasDerivAt (fun t : ℝ => Real.sin (b * t))
      (b * Real.cos (b * x)) x := by
    convert (Real.hasDerivAt_sin (b * x)).comp x harg using 1 <;> ring
  have ht : HasDerivAt
      (fun t : ℝ => a * Real.cos (b * t) + b * Real.sin (b * t))
      (a * (-b * Real.sin (b * x)) + b * (b * Real.cos (b * x))) x := by
    exact (hc.const_mul a).add (hs.const_mul b)
  unfold primitive cosIntegrand
  convert (he.mul ht).div_const (a ^ 2 + b ^ 2) using 1
  field_simp [hden]
  ring

private theorem boundary₁_hasDerivAt (a b : ℝ) (ha : a ≠ 0) (x : ℝ) :
    HasDerivAt (boundary₁ a b)
      (cosIntegrand a b x - b / a * sinIntegrand a b x) x := by
  have he := hasDerivAt_exp_mul a x
  have harg : HasDerivAt (fun t : ℝ => b * t) b x := by
    simpa using (hasDerivAt_id x).const_mul b
  have hc : HasDerivAt (fun t : ℝ => Real.cos (b * t))
      (-b * Real.sin (b * x)) x := by
    convert (Real.hasDerivAt_cos (b * x)).comp x harg using 1 <;> ring
  have hd := (he.mul hc).const_mul (1 / a)
  convert hd using 1
  · funext y
    simp [boundary₁]
    ring
  · unfold cosIntegrand sinIntegrand
    field_simp [ha]
    ring

private theorem boundary₂_hasDerivAt (a b : ℝ) (ha : a ≠ 0) (x : ℝ) :
    HasDerivAt (boundary₂ a b)
      ((1 + b ^ 2 / a ^ 2) * cosIntegrand a b x) x := by
  have he := hasDerivAt_exp_mul a x
  have harg : HasDerivAt (fun t : ℝ => b * t) b x := by
    simpa using (hasDerivAt_id x).const_mul b
  have hs : HasDerivAt (fun t : ℝ => Real.sin (b * t))
      (b * Real.cos (b * x)) x := by
    convert (Real.hasDerivAt_sin (b * x)).comp x harg using 1 <;> ring
  have hsecond :=
    (he.mul hs).const_mul (b / a ^ 2)
  have hsecond' :
      HasDerivAt
        (fun t : ℝ =>
          b / a ^ 2 * Real.exp (a * t) * Real.sin (b * t))
        (b / a ^ 2 *
          (a * Real.exp (a * x) * Real.sin (b * x) +
            Real.exp (a * x) * (b * Real.cos (b * x)))) x := by
    convert hsecond using 1
    funext y
    simp
    ring
  have hd := (boundary₁_hasDerivAt a b ha x).add hsecond'
  convert hd using 1
  · unfold cosIntegrand sinIntegrand
    field_simp [ha]
    ring

private theorem antiderivatives_eq_primitive_of_hasDerivAt
    (f p : ℝ → ℝ) (hp : ∀ x, HasDerivAt p (f x) x) :
    AntiderivativesOn f = PrimitiveFamily p := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (f x) x at hF
    change ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C
    have hzero : ∀ x, HasDerivAt (fun y => F y - p y) 0 x := by
      intro x
      convert (hF x (by simp [branch])).sub (hp x) using 1
      ring
    have hdiff : Differentiable ℝ (fun y => F y - p y) := by
      intro x
      exact (hzero x).differentiableAt
    have hconst : ∀ x, F x - p x = F 0 - p 0 := by
      intro x
      exact is_const_of_deriv_eq_zero hdiff (fun y => (hzero y).deriv) x 0
    refine ⟨F 0 - p 0, ?_⟩
    intro x hx
    have hxconst := hconst x
    linarith
  · rintro ⟨C, hC⟩
    change ∀ x ∈ branch, HasDerivAt F (f x) x
    have hfun : F = fun x => p x + C := by
      funext x
      exact hC x (by simp [branch])
    rw [hfun]
    intro x hx
    simpa using (hp x).add_const C

private theorem antiderivatives_eq_byParts (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    AntiderivativesOn (cosIntegrand a b) = ByPartsFamily a b := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (cosIntegrand a b x) x at hF
    change ∃ G ∈ AntiderivativesOn (sinIntegrand a b),
      ∀ x ∈ branch, F x = boundary₁ a b x + b / a * G x
    refine ⟨fun x => (a / b) * (F x - boundary₁ a b x), ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun x => (a / b) * (F x - boundary₁ a b x))
          (sinIntegrand a b x) x
      intro x hx
      have hd :=
        ((hF x hx).sub (boundary₁_hasDerivAt a b ha x)).const_mul
          (a / b)
      convert hd using 1 <;> field_simp [ha, hb] <;> ring
    · intro x hx
      field_simp [ha, hb]
      ring
  · rintro ⟨G, hG, hFG⟩
    change ∀ x ∈ branch, HasDerivAt F (cosIntegrand a b x) x
    have hfun : F = fun x => boundary₁ a b x + b / a * G x := by
      funext x
      exact hFG x (by simp [branch])
    rw [hfun]
    intro x hx
    have hd :=
      (boundary₁_hasDerivAt a b ha x).add
        ((hG x hx).const_mul (b / a))
    convert hd using 1 <;> field_simp [ha] <;> ring

private theorem antiderivatives_eq_recurrence (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    AntiderivativesOn (cosIntegrand a b) = RecurrenceFamily a b := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (cosIntegrand a b x) x at hF
    change ∃ G ∈ AntiderivativesOn (cosIntegrand a b),
      ∀ x ∈ branch, F x = boundary₂ a b x - b ^ 2 / a ^ 2 * G x
    refine ⟨fun x => (a ^ 2 / b ^ 2) * (boundary₂ a b x - F x), ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt
          (fun x => (a ^ 2 / b ^ 2) * (boundary₂ a b x - F x))
          (cosIntegrand a b x) x
      intro x hx
      have hd :=
        ((boundary₂_hasDerivAt a b ha x).sub (hF x hx)).const_mul
          (a ^ 2 / b ^ 2)
      convert hd using 1 <;> field_simp [ha, hb] <;> ring
    · intro x hx
      field_simp [ha, hb]
      ring
  · rintro ⟨G, hG, hFG⟩
    change ∀ x ∈ branch, HasDerivAt F (cosIntegrand a b x) x
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
    AntiderivativesOn (cosIntegrand a b) =
      PrimitiveFamily (fun x => x) := by
  subst a
  subst b
  apply antiderivatives_eq_primitive_of_hasDerivAt
  intro x
  simpa [cosIntegrand] using (hasDerivAt_id x)
theorem gap2 (a b : ℝ) (ha : a = 0) (hb : b ≠ 0) :
    AntiderivativesOn (cosIntegrand a b) =
      PrimitiveFamily (fun x => (1 / b) * Real.sin (b * x)) := by
  subst a
  apply antiderivatives_eq_primitive_of_hasDerivAt
  intro x
  have harg : HasDerivAt (fun t : ℝ => b * t) b x := by
    simpa using (hasDerivAt_id x).const_mul b
  have hs : HasDerivAt (fun t : ℝ => Real.sin (b * t))
      (b * Real.cos (b * x)) x := by
    convert (Real.hasDerivAt_sin (b * x)).comp x harg using 1 <;> ring
  convert hs.const_mul (1 / b) using 1 <;>
    simp [cosIntegrand, hb] <;> field_simp [hb] <;> ring
theorem gap3 (a b : ℝ) (ha : a ≠ 0) :
    AntiderivativesOn (cosIntegrand a b) =
      ScaledFamily (1 / a) (expCosChain a b) := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (cosIntegrand a b x) x at hF
    change ∃ G ∈ AntiderivativesOn (expCosChain a b),
      ∀ x ∈ branch, F x = (1 / a) * G x
    refine ⟨fun x => a * F x, ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun x => a * F x) (expCosChain a b x) x
      intro x hx
      rw [expCosChain_eq]
      simpa using (hF x hx).const_mul a
    · intro x hx
      field_simp [ha]
  · rintro ⟨G, hG, hFG⟩
    change ∀ x ∈ branch, HasDerivAt F (cosIntegrand a b x) x
    have hfun : F = fun x => (1 / a) * G x := by
      funext x
      exact hFG x (by simp [branch])
    rw [hfun]
    intro x hx
    have hd := (hG x hx).const_mul (1 / a)
    rw [expCosChain_eq] at hd
    convert hd using 1 <;> field_simp [ha]
theorem gap4 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ScaledFamily (1 / a) (expCosChain a b) =
      ByPartsFamily a b := by
  calc
    ScaledFamily (1 / a) (expCosChain a b) =
        AntiderivativesOn (cosIntegrand a b) := (gap3 a b ha).symm
    _ = ByPartsFamily a b := antiderivatives_eq_byParts a b ha hb
theorem gap5 (a b : ℝ) (ha : a ≠ 0) :
    ByPartsFamily a b = SecondChainFamily a b := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    change ∃ H ∈ AntiderivativesOn (expSinChain a b),
      ∀ x ∈ branch, F x = boundary₁ a b x + b / a ^ 2 * H x
    refine ⟨fun x => a * G x, ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun x => a * G x) (expSinChain a b x) x
      intro x hx
      rw [expSinChain_eq]
      simpa using (hG x hx).const_mul a
    · intro x hx
      rw [hFG x hx]
      field_simp [ha]
  · rintro ⟨G, hG, hFG⟩
    change ∃ H ∈ AntiderivativesOn (sinIntegrand a b),
      ∀ x ∈ branch, F x = boundary₁ a b x + b / a * H x
    refine ⟨fun x => (1 / a) * G x, ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun x => (1 / a) * G x) (sinIntegrand a b x) x
      intro x hx
      have hd := (hG x hx).const_mul (1 / a)
      rw [expSinChain_eq] at hd
      convert hd using 1 <;> field_simp [ha]
    · intro x hx
      rw [hFG x hx]
      field_simp [ha]
theorem gap6 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    AntiderivativesOn (cosIntegrand a b) =
      SecondChainFamily a b := by
  calc
    AntiderivativesOn (cosIntegrand a b) =
        ScaledFamily (1 / a) (expCosChain a b) := gap3 a b ha
    _ = ByPartsFamily a b := gap4 a b ha hb
    _ = SecondChainFamily a b := gap5 a b ha
theorem gap7 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    AntiderivativesOn (cosIntegrand a b) =
      RecurrenceFamily a b := by
  exact antiderivatives_eq_recurrence a b ha hb
theorem gap8 (a b : ℝ) (ha : a ≠ 0) :
    AntiderivativesOn (cosIntegrand a b) =
      PrimitiveFamily (primitiveRaw a b) := by
  have hden : a ^ 2 + b ^ 2 ≠ 0 := sum_sq_ne_zero_left ha
  have hfun : primitiveRaw a b = primitive a b := by
    funext x
    unfold primitiveRaw primitive
    field_simp [ha, hden]
  rw [hfun]
  apply antiderivatives_eq_primitive_of_hasDerivAt
  intro x
  exact primitive_hasDerivAt a b ha x
theorem gap9 (a b : ℝ) (ha : a ≠ 0) :
    PrimitiveFamily (primitiveRaw a b) =
      PrimitiveFamily (primitive a b) := by
  have hden : a ^ 2 + b ^ 2 ≠ 0 := sum_sq_ne_zero_left ha
  have hfun : primitiveRaw a b = primitive a b := by
    funext x
    unfold primitiveRaw primitive
    field_simp [ha, hden]
  rw [hfun]
theorem gap10 (a b : ℝ) (ha : a ≠ 0) :
    AntiderivativesOn (cosIntegrand a b) =
      PrimitiveFamily (primitive a b) := by
  calc
    AntiderivativesOn (cosIntegrand a b) =
        PrimitiveFamily (primitiveRaw a b) := gap8 a b ha
    _ = PrimitiveFamily (primitive a b) := gap9 a b ha

end
end ProofGap.Exercise1828
