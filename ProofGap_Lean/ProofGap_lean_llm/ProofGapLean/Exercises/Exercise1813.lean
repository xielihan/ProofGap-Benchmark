import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1813

noncomputable section

def branch : Set ℝ := Set.univ
def integrand (x : ℝ) := x * (Real.arctan x) ^ 2
def scaledIntegrand (x : ℝ) :=
  (Real.arctan x) ^ 2 * deriv (fun t : ℝ => t ^ 2) x
def residual₁ (x : ℝ) := x ^ 2 * Real.arctan x / (1 + x ^ 2)
def residual₂ (x : ℝ) :=
  (1 - 1 / (1 + x ^ 2)) * Real.arctan x
def arctanIntegrand (x : ℝ) := Real.arctan x
def arctanChainIntegrand (x : ℝ) :=
  Real.arctan x * deriv Real.arctan x
def logResidual (x : ℝ) := x / (1 + x ^ 2)
def boundary₁ (x : ℝ) := x ^ 2 / 2 * (Real.arctan x) ^ 2
def boundary₂ (x : ℝ) :=
  boundary₁ x - x * Real.arctan x + (1 / 2 : ℝ) * (Real.arctan x) ^ 2
def primitive (x : ℝ) :=
  (x ^ 2 + 1) / 2 * (Real.arctan x) ^ 2 -
    x * Real.arctan x + (1 / 2 : ℝ) * Real.log (1 + x ^ 2)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def HalfFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn scaledIntegrand,
    ∀ x ∈ branch, F x = (1 / 2 : ℝ) * G x}
def ByPartsFamily (b : ℝ → ℝ) (c : ℝ) (r : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn r, ∀ x ∈ branch, F x = b x + c * G x}
def SplitFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn arctanIntegrand,
    ∃ H ∈ AntiderivativesOn arctanChainIntegrand,
      ∀ x ∈ branch, F x = boundary₁ x - G x + H x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private lemma one_add_sq_pos (x : ℝ) : 0 < 1 + x ^ 2 := by
  positivity

private lemma deriv_square (x : ℝ) :
    deriv (fun t : ℝ => t ^ 2) x = 2 * x := by
  simpa using ((hasDerivAt_id x).pow 2).deriv

private lemma hasDerivAt_boundary₁ (x : ℝ) :
    HasDerivAt boundary₁ (integrand x + residual₁ x) x := by
  have h := (((hasDerivAt_id x).pow 2).div_const 2).mul
    ((Real.hasDerivAt_arctan x).pow 2)
  simp at h
  unfold boundary₁ integrand residual₁
  convert h using 1
  field_simp [ne_of_gt (one_add_sq_pos x)] <;> ring

private lemma residual₁_eq_residual₂ : residual₁ = residual₂ := by
  funext x
  unfold residual₁ residual₂
  field_simp [ne_of_gt (one_add_sq_pos x)]
  ring

private def chainPrimitive (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (Real.arctan x) ^ 2

private lemma hasDerivAt_chainPrimitive (x : ℝ) :
    HasDerivAt chainPrimitive (arctanChainIntegrand x) x := by
  have h := ((Real.hasDerivAt_arctan x).pow 2).const_mul (1 / 2 : ℝ)
  unfold chainPrimitive arctanChainIntegrand
  convert h using 1
  rw [(Real.hasDerivAt_arctan x).deriv]
  ring

private lemma residual₂_add_chain (x : ℝ) :
    residual₂ x + arctanChainIntegrand x = arctanIntegrand x := by
  unfold residual₂ arctanChainIntegrand arctanIntegrand
  rw [(Real.hasDerivAt_arctan x).deriv]
  field_simp [ne_of_gt (one_add_sq_pos x)]
  ring

private lemma arctan_sub_chain (x : ℝ) :
    arctanIntegrand x - arctanChainIntegrand x = residual₂ x := by
  have h := residual₂_add_chain x
  linarith

private lemma hasDerivAt_boundary₂ (x : ℝ) :
    HasDerivAt boundary₂ (integrand x - logResidual x) x := by
  have ha := Real.hasDerivAt_arctan x
  have h := ((hasDerivAt_boundary₁ x).sub
    ((hasDerivAt_id x).mul ha)).add (hasDerivAt_chainPrimitive x)
  simp at h
  unfold boundary₂
  convert h using 1
  unfold integrand residual₁ logResidual arctanChainIntegrand
  rw [ha.deriv]
  field_simp [ne_of_gt (one_add_sq_pos x)]
  ring

private def logPrimitive (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (1 + x ^ 2)

private lemma hasDerivAt_logPrimitive (x : ℝ) :
    HasDerivAt logPrimitive (logResidual x) x := by
  have hi := (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2)
  have hl := (Real.hasDerivAt_log (ne_of_gt (one_add_sq_pos x))).comp x hi
  have h := hl.const_mul (1 / 2 : ℝ)
  simp at h
  unfold logPrimitive logResidual
  convert h using 1
  field_simp [ne_of_gt (one_add_sq_pos x)]
  ring

private lemma primitive_eq_boundary₂_add_logPrimitive (x : ℝ) :
    primitive x = boundary₂ x + logPrimitive x := by
  unfold primitive boundary₂ boundary₁ logPrimitive
  ring

private lemma exists_constant_of_hasDerivAt_zero
    (f : ℝ → ℝ) (hf : ∀ x, HasDerivAt f 0 x) :
    ∃ C : ℝ, ∀ x, f x = C := by
  have hdiff : Differentiable ℝ f := fun x => (hf x).differentiableAt
  have hderiv : ∀ x, deriv f x = 0 := fun x => (hf x).deriv
  have hconst := is_const_of_deriv_eq_zero hdiff hderiv
  exact ⟨f 0, fun x => hconst x 0⟩

theorem gap1 :
    AntiderivativesOn integrand = HalfFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ G ∈ AntiderivativesOn scaledIntegrand,
      ∀ x ∈ branch, F x = (1 / 2 : ℝ) * G x
    refine ⟨fun x => 2 * F x, ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun y => 2 * F y) (scaledIntegrand x) x
      intro x hx
      have h := (hF x hx).const_mul 2
      convert h using 1
      unfold scaledIntegrand integrand
      rw [deriv_square]
      ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    have hEq : F = fun x => (1 / 2 : ℝ) * G x := by
      funext x
      exact hFG x (by simp [branch])
    rw [hEq]
    intro x hx
    have h := (hG x hx).const_mul (1 / 2 : ℝ)
    convert h using 1
    unfold scaledIntegrand integrand
    rw [deriv_square]
    ring
theorem gap2 :
    HalfFamily = ByPartsFamily boundary₁ (-1) residual₁ := by
  ext F
  constructor
  · intro hF
    have hFi : F ∈ AntiderivativesOn integrand := by
      rw [gap1]
      exact hF
    change ∃ R ∈ AntiderivativesOn residual₁,
      ∀ x ∈ branch, F x = boundary₁ x + (-1 : ℝ) * R x
    refine ⟨fun x => boundary₁ x - F x, ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun y => boundary₁ y - F y) (residual₁ x) x
      intro x hx
      convert (hasDerivAt_boundary₁ x).sub (hFi x hx) using 1 <;> ring
    · intro x hx
      ring
  · rintro ⟨R, hR, hFR⟩
    apply (Set.ext_iff.mp gap1 F).mp
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    have hEq : F = fun x => boundary₁ x - R x := by
      funext x
      simpa using hFR x (by simp [branch])
    rw [hEq]
    intro x hx
    convert (hasDerivAt_boundary₁ x).sub (hR x hx) using 1 <;> ring
theorem gap3 :
    AntiderivativesOn integrand =
      ByPartsFamily boundary₁ (-1) residual₁ := by
  exact gap1.trans gap2
theorem gap4 :
    AntiderivativesOn integrand =
      ByPartsFamily boundary₁ (-1) residual₂ := by
  rw [gap3, residual₁_eq_residual₂]
theorem gap5 :
    ByPartsFamily boundary₁ (-1) residual₂ = SplitFamily := by
  ext F
  constructor
  · rintro ⟨R, hR, hFR⟩
    change ∃ G ∈ AntiderivativesOn arctanIntegrand,
      ∃ H ∈ AntiderivativesOn arctanChainIntegrand,
        ∀ x ∈ branch, F x = boundary₁ x - G x + H x
    refine ⟨fun x => R x + chainPrimitive x, ?_, chainPrimitive, ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun y => R y + chainPrimitive y)
          (arctanIntegrand x) x
      intro x hx
      convert (hR x hx).add (hasDerivAt_chainPrimitive x) using 1
      exact (residual₂_add_chain x).symm
    · exact fun x hx => hasDerivAt_chainPrimitive x
    · intro x hx
      have h := hFR x hx
      ring_nf at h ⊢
      linarith
  · rintro ⟨G, hG, H, hH, hFGH⟩
    change ∃ R ∈ AntiderivativesOn residual₂,
      ∀ x ∈ branch, F x = boundary₁ x + (-1 : ℝ) * R x
    refine ⟨fun x => G x - H x, ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun y => G y - H y) (residual₂ x) x
      intro x hx
      convert (hG x hx).sub (hH x hx) using 1
      exact (arctan_sub_chain x).symm
    · intro x hx
      have h := hFGH x hx
      ring_nf at h ⊢
      linarith
theorem gap6 :
    AntiderivativesOn integrand = SplitFamily := by
  exact gap4.trans gap5
theorem gap7 :
    AntiderivativesOn integrand =
      ByPartsFamily boundary₂ 1 logResidual := by
  ext F
  constructor
  · intro hF
    change ∃ R ∈ AntiderivativesOn logResidual,
      ∀ x ∈ branch, F x = boundary₂ x + (1 : ℝ) * R x
    refine ⟨fun x => F x - boundary₂ x, ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun y => F y - boundary₂ y) (logResidual x) x
      intro x hx
      convert (hF x hx).sub (hasDerivAt_boundary₂ x) using 1 <;> ring
    · intro x hx
      ring
  · rintro ⟨R, hR, hFR⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    have hEq : F = fun x => boundary₂ x + R x := by
      funext x
      simpa using hFR x (by simp [branch])
    rw [hEq]
    intro x hx
    convert (hasDerivAt_boundary₂ x).add (hR x hx) using 1 <;> ring
theorem gap8 :
    ByPartsFamily boundary₂ 1 logResidual = PrimitiveFamily := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    have hz : ∀ x, HasDerivAt (fun y => G y - logPrimitive y) 0 x := by
      intro x
      convert (hG x (by simp [branch])).sub (hasDerivAt_logPrimitive x) using 1
      ring
    obtain ⟨C, hC⟩ := exists_constant_of_hasDerivAt_zero
      (fun x => G x - logPrimitive x) hz
    change ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
    refine ⟨C, ?_⟩
    intro x hx
    have hGx : G x = logPrimitive x + C := by
      have := hC x
      linarith
    calc
      F x = boundary₂ x + G x := by simpa using hFG x hx
      _ = boundary₂ x + (logPrimitive x + C) := by rw [hGx]
      _ = primitive x + C := by
        rw [primitive_eq_boundary₂_add_logPrimitive]
        ring
  · rintro ⟨C, hFC⟩
    change ∃ G ∈ AntiderivativesOn logResidual,
      ∀ x ∈ branch, F x = boundary₂ x + (1 : ℝ) * G x
    refine ⟨fun x => logPrimitive x + C, ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun y => logPrimitive y + C) (logResidual x) x
      intro x hx
      exact (hasDerivAt_logPrimitive x).add_const C
    · intro x hx
      calc
        F x = primitive x + C := hFC x hx
        _ = boundary₂ x + (1 : ℝ) * (logPrimitive x + C) := by
          rw [primitive_eq_boundary₂_add_logPrimitive]
          ring
theorem gap9 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  exact gap7.trans gap8

end
end ProofGap.Exercise1813
