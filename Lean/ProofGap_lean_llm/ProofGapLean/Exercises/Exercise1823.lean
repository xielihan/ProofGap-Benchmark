import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1823

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def t (x : ℝ) := Real.sqrt x
def integrand (x : ℝ) := x * Real.sin (t x)
def substitutedIntegrand (x : ℝ) :=
  (t x) ^ 3 * Real.sin (t x) * deriv t x
def cosineChain₃ (x : ℝ) := (t x) ^ 3 * deriv (fun y => Real.cos (t y)) x
def residual₂ (x : ℝ) := (t x) ^ 2 * Real.cos (t x) * deriv t x
def sineChain₂ (x : ℝ) := (t x) ^ 2 * deriv (fun y => Real.sin (t y)) x
def residual₁ (x : ℝ) := t x * Real.sin (t x) * deriv t x
def cosineChain₁ (x : ℝ) := t x * deriv (fun y => Real.cos (t y)) x
def cosineResidual (x : ℝ) := Real.cos (t x) * deriv t x
def boundary₁ (x : ℝ) := -2 * (t x) ^ 3 * Real.cos (t x)
def boundary₂ (x : ℝ) :=
  boundary₁ x + 6 * (t x) ^ 2 * Real.sin (t x)
def boundary₃ (x : ℝ) := boundary₂ x + 12 * t x * Real.cos (t x)
def primitiveT (x : ℝ) :=
  -2 * ((t x) ^ 2 - 6) * t x * Real.cos (t x) +
    6 * ((t x) ^ 2 - 2) * Real.sin (t x)
def primitive (x : ℝ) :=
  2 * (6 - x) * Real.sqrt x * Real.cos (Real.sqrt x) -
    6 * (2 - x) * Real.sin (Real.sqrt x)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ScaledFamily (c : ℝ) (b : ℝ → ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn f, ∀ x ∈ branch, F x = b x + c * G x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem hasDerivAt_t (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt t (deriv t x) x := by
  have hx' : 0 < x := by simpa [branch] using hx
  have hdiff : DifferentiableAt ℝ t x := by
    simpa [t] using (Real.hasDerivAt_sqrt hx'.ne').differentiableAt
  exact hdiff.hasDerivAt

private theorem hasDerivAt_sin_t (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y => Real.sin (t y)) (cosineResidual x) x := by
  have h := (Real.hasDerivAt_sin (t x)).comp x (hasDerivAt_t x hx)
  simpa [cosineResidual] using h

private theorem deriv_cos_t (x : ℝ) (hx : x ∈ branch) :
    deriv (fun y => Real.cos (t y)) x = -Real.sin (t x) * deriv t x := by
  exact ((Real.hasDerivAt_cos (t x)).comp x (hasDerivAt_t x hx)).deriv

private theorem deriv_sin_t (x : ℝ) (hx : x ∈ branch) :
    deriv (fun y => Real.sin (t y)) x = Real.cos (t x) * deriv t x := by
  exact ((Real.hasDerivAt_sin (t x)).comp x (hasDerivAt_t x hx)).deriv

private theorem integrand_eq_two_substituted (x : ℝ) (hx : x ∈ branch) :
    integrand x = 2 * substitutedIntegrand x := by
  have hx' : 0 < x := by simpa [branch] using hx
  have ht : t x ≠ 0 := by
    simpa [t] using (Real.sqrt_pos.2 hx').ne'
  have hsq : x = (t x) ^ 2 := by
    simpa [t] using (Real.sq_sqrt (le_of_lt hx')).symm
  have hd : deriv t x = 1 / (2 * t x) := by
    simpa [t] using (Real.hasDerivAt_sqrt hx'.ne').deriv
  have hi : integrand x = (t x) ^ 2 * Real.sin (t x) := by
    change x * Real.sin (t x) = (t x) ^ 2 * Real.sin (t x)
    exact congrArg (fun z : ℝ => z * Real.sin (t x)) hsq
  rw [hi, substitutedIntegrand, hd]
  field_simp [ht] <;> ring_nf

private theorem cosineChain_three_eq (x : ℝ) (hx : x ∈ branch) :
    cosineChain₃ x = -substitutedIntegrand x := by
  rw [cosineChain₃, substitutedIntegrand, deriv_cos_t x hx]
  ring

private theorem sineChain_two_eq (x : ℝ) (hx : x ∈ branch) :
    sineChain₂ x = residual₂ x := by
  rw [sineChain₂, residual₂, deriv_sin_t x hx]
  ring

private theorem cosineChain_one_eq (x : ℝ) (hx : x ∈ branch) :
    cosineChain₁ x = -residual₁ x := by
  rw [cosineChain₁, residual₁, deriv_cos_t x hx]
  ring

private theorem scaledFamily_eq_antiderivativesOn
    (c : ℝ) (b f q : ℝ → ℝ) (hc : c ≠ 0)
    (hb : ∀ x ∈ branch, HasDerivAt b (q x - c * f x) x) :
    ScaledFamily c b f = AntiderivativesOn q := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hr := (hb x hx).add ((hG x hx).const_mul c)
    have hr' : HasDerivAt (fun y => b y + c * G y) (q x) x := by
      convert hr using 1 <;> ring
    apply hr'.congr_of_eventuallyEq
    have hx' : x ∈ Set.Ioi (0 : ℝ) := by simpa [branch] using hx
    filter_upwards [isOpen_Ioi.mem_nhds hx'] with y hy
    exact hFG y (by simpa [branch] using hy)
  · intro hF
    refine ⟨fun y => (F y - b y) / c, ?_, ?_⟩
    · intro x hx
      have hd := (hF x hx).sub (hb x hx)
      have hd' : HasDerivAt (fun y => F y - b y) (c * f x) x := by
        convert hd using 1 <;> ring
      convert hd'.div_const c using 1
      field_simp [hc]
    · intro x hx
      field_simp [hc]
      <;> ring

private theorem hasDerivAt_boundary_one (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt boundary₁ (integrand x - 6 * residual₂ x) x := by
  have ht := hasDerivAt_t x hx
  have hc := (Real.hasDerivAt_cos (t x)).comp x ht
  have h := ((ht.pow 3).mul hc).const_mul (-2)
  have hi := integrand_eq_two_substituted x hx
  convert h using 1
  · funext y
    simp [boundary₁] <;> ring_nf
  · rw [hi]
    simp [substitutedIntegrand, residual₂] <;> ring_nf

private theorem hasDerivAt_boundary_two (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt boundary₂ (integrand x + 12 * residual₁ x) x := by
  have ht := hasDerivAt_t x hx
  have hs := (Real.hasDerivAt_sin (t x)).comp x ht
  have hterm := ((ht.pow 2).mul hs).const_mul 6
  have h := (hasDerivAt_boundary_one x hx).add hterm
  convert h using 1
  · funext y
    simp [boundary₂] <;> ring_nf
  · simp [residual₁, residual₂] <;> ring_nf

private theorem hasDerivAt_boundary_three (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt boundary₃ (integrand x + 12 * cosineResidual x) x := by
  have ht := hasDerivAt_t x hx
  have hc := (Real.hasDerivAt_cos (t x)).comp x ht
  have hterm := (ht.mul hc).const_mul 12
  have h := (hasDerivAt_boundary_two x hx).add hterm
  convert h using 1
  · funext y
    simp [boundary₃] <;> ring_nf
  · simp [residual₁, cosineResidual] <;> ring_nf

private theorem primitiveT_boundary_identity (x : ℝ) :
    primitiveT x = boundary₃ x - 12 * Real.sin (t x) := by
  simp [primitiveT, boundary₃, boundary₂, boundary₁]
  ring

private theorem cosineResidual_antiderivative_constant
    (G : ℝ → ℝ) (hG : G ∈ AntiderivativesOn cosineResidual) :
    ∃ C : ℝ, ∀ x ∈ branch, G x = Real.sin (t x) + C := by
  let H : ℝ → ℝ := fun z => G (Real.exp z) - Real.sin (t (Real.exp z))
  have hH : ∀ z : ℝ, HasDerivAt H 0 z := by
    intro z
    have hz : Real.exp z ∈ branch := by
      simpa [branch] using Real.exp_pos z
    have hzero := (hG (Real.exp z) hz).sub (hasDerivAt_sin_t (Real.exp z) hz)
    have hcomp := hzero.comp z (Real.hasDerivAt_exp z)
    convert hcomp using 1 <;> simp [H]
  refine ⟨H 0, ?_⟩
  intro x hx
  have hx' : 0 < x := by simpa [branch] using hx
  have heq : H (Real.log x) = H 0 :=
    is_const_of_deriv_eq_zero
      (fun z => (hH z).differentiableAt)
      (fun z => (hH z).deriv)
      (Real.log x) 0
  dsimp [H] at heq ⊢
  rw [Real.exp_log hx'] at heq
  norm_num at heq ⊢
  linarith

private theorem primitiveT_eq_primitive (x : ℝ) (hx : x ∈ branch) :
    primitiveT x = primitive x := by
  have hx' : 0 ≤ x := le_of_lt (by simpa [branch] using hx)
  have hs := Real.sq_sqrt hx'
  simp [primitiveT, primitive, t]
  rw [hs]
  ring

theorem gap1 (x : ℝ) (hx : x ∈ branch) :
    x = (t x) ^ 2 := by
  exact (Real.sq_sqrt (le_of_lt (by simpa [branch] using hx))).symm
theorem gap2 (x : ℝ) (hx : x ∈ branch) :
    deriv (fun y : ℝ => y) x = 2 * t x * deriv t x := by
  have hx' : 0 < x := by simpa [branch] using hx
  have ht : t x ≠ 0 := by
    simpa [t] using (Real.sqrt_pos.2 hx').ne'
  have hd : deriv t x = 1 / (2 * t x) := by
    simpa [t] using (Real.hasDerivAt_sqrt hx'.ne').deriv
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  rw [hid.deriv, hd]
  field_simp [ht]
theorem gap3 :
    AntiderivativesOn integrand =
      ScaledFamily 2 (fun _ => 0) substitutedIntegrand := by
  exact (scaledFamily_eq_antiderivativesOn 2 (fun _ => 0) substitutedIntegrand integrand (by norm_num) (by
    intro x hx
    have h0 : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (0 : ℝ) x :=
      hasDerivAt_const x (0 : ℝ)
    convert h0 using 1
    rw [integrand_eq_two_substituted x hx]
    ring)).symm
theorem gap4 :
    ScaledFamily 2 (fun _ => 0) substitutedIntegrand =
      ScaledFamily (-2) (fun _ => 0) cosineChain₃ := by
  calc
    ScaledFamily 2 (fun _ => 0) substitutedIntegrand = AntiderivativesOn integrand := gap3.symm
    _ = ScaledFamily (-2) (fun _ => 0) cosineChain₃ :=
      (scaledFamily_eq_antiderivativesOn (-2) (fun _ => 0) cosineChain₃ integrand (by norm_num) (by
        intro x hx
        have h0 : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (0 : ℝ) x :=
          hasDerivAt_const x (0 : ℝ)
        convert h0 using 1
        rw [integrand_eq_two_substituted x hx, cosineChain_three_eq x hx]
        ring)).symm
theorem gap5 :
    ScaledFamily (-2) (fun _ => 0) cosineChain₃ =
      ScaledFamily 6 boundary₁ residual₂ := by
  calc
    ScaledFamily (-2) (fun _ => 0) cosineChain₃ = AntiderivativesOn integrand :=
      gap4.symm.trans gap3.symm
    _ = ScaledFamily 6 boundary₁ residual₂ :=
      (scaledFamily_eq_antiderivativesOn 6 boundary₁ residual₂ integrand (by norm_num) (by
        intro x hx
        exact hasDerivAt_boundary_one x hx)).symm
theorem gap6 :
    ScaledFamily 6 boundary₁ residual₂ =
      ScaledFamily 6 boundary₁ sineChain₂ := by
  calc
    ScaledFamily 6 boundary₁ residual₂ = AntiderivativesOn integrand :=
      scaledFamily_eq_antiderivativesOn 6 boundary₁ residual₂ integrand (by norm_num) (by
        intro x hx
        exact hasDerivAt_boundary_one x hx)
    _ = ScaledFamily 6 boundary₁ sineChain₂ :=
      (scaledFamily_eq_antiderivativesOn 6 boundary₁ sineChain₂ integrand (by norm_num) (by
        intro x hx
        convert hasDerivAt_boundary_one x hx using 1
        rw [sineChain_two_eq x hx])).symm
theorem gap7 :
    AntiderivativesOn integrand =
      ScaledFamily 6 boundary₁ sineChain₂ := by
  exact gap3.trans (gap4.trans (gap5.trans gap6))
theorem gap8 :
    AntiderivativesOn integrand =
      ScaledFamily (-12) boundary₂ residual₁ := by
  exact (scaledFamily_eq_antiderivativesOn (-12) boundary₂ residual₁ integrand (by norm_num) (by
    intro x hx
    convert hasDerivAt_boundary_two x hx using 1 <;> ring)).symm
theorem gap9 :
    ScaledFamily (-12) boundary₂ residual₁ =
      ScaledFamily 12 boundary₂ cosineChain₁ := by
  calc
    ScaledFamily (-12) boundary₂ residual₁ = AntiderivativesOn integrand :=
      scaledFamily_eq_antiderivativesOn (-12) boundary₂ residual₁ integrand (by norm_num) (by
        intro x hx
        convert hasDerivAt_boundary_two x hx using 1 <;> ring)
    _ = ScaledFamily 12 boundary₂ cosineChain₁ :=
      (scaledFamily_eq_antiderivativesOn 12 boundary₂ cosineChain₁ integrand (by norm_num) (by
        intro x hx
        convert hasDerivAt_boundary_two x hx using 1
        rw [cosineChain_one_eq x hx]
        ring)).symm
theorem gap10 :
    AntiderivativesOn integrand =
      ScaledFamily 12 boundary₂ cosineChain₁ := by
  exact gap8.trans gap9
theorem gap11 :
    AntiderivativesOn integrand =
      ScaledFamily (-12) boundary₃ cosineResidual := by
  exact (scaledFamily_eq_antiderivativesOn (-12) boundary₃ cosineResidual integrand (by norm_num) (by
    intro x hx
    convert hasDerivAt_boundary_three x hx using 1 <;> ring)).symm
theorem gap12 :
    ScaledFamily (-12) boundary₃ cosineResidual =
      PrimitiveFamily primitiveT := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    obtain ⟨C, hC⟩ := cosineResidual_antiderivative_constant G hG
    refine ⟨-12 * C, ?_⟩
    intro x hx
    rw [hFG x hx, hC x hx, primitiveT_boundary_identity x]
    ring
  · rintro ⟨C, hFC⟩
    refine ⟨fun x => Real.sin (t x) - C / 12, ?_, ?_⟩
    · intro x hx
      have hs := hasDerivAt_sin_t x hx
      convert hs.sub_const (C / 12) using 1 <;> simp [cosineResidual]
    · intro x hx
      rw [hFC x hx, primitiveT_boundary_identity x]
      ring
theorem gap13 :
    AntiderivativesOn integrand = PrimitiveFamily primitiveT := by
  exact gap11.trans gap12
theorem gap14 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  calc
    AntiderivativesOn integrand = PrimitiveFamily primitiveT := gap13
    _ = PrimitiveFamily primitive := by
      ext F
      constructor
      · rintro ⟨C, hF⟩
        refine ⟨C, ?_⟩
        intro x hx
        rw [hF x hx, primitiveT_eq_primitive x hx]
      · rintro ⟨C, hF⟩
        refine ⟨C, ?_⟩
        intro x hx
        rw [hF x hx, primitiveT_eq_primitive x hx]

end
end ProofGap.Exercise1823
