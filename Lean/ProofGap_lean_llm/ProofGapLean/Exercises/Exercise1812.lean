import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1812

noncomputable section

def branch : Set ℝ := Set.Ioo (-1 : ℝ) 1
def integrand (x : ℝ) := (Real.arcsin x) ^ 2
def residual₁ (x : ℝ) :=
  x * Real.arcsin x / Real.sqrt (1 - x ^ 2)
def residual₂ (x : ℝ) :=
  Real.arcsin x * deriv (fun t : ℝ => Real.sqrt (1 - t ^ 2)) x
def boundary₁ (x : ℝ) := x * (Real.arcsin x) ^ 2
def boundary₂ (x : ℝ) :=
  boundary₁ x + 2 * Real.sqrt (1 - x ^ 2) * Real.arcsin x
def primitive (x : ℝ) := boundary₂ x - 2 * x
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ByPartsFamily (b : ℝ → ℝ) (c : ℝ) (r : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn r, ∀ x ∈ branch, F x = b x + c * G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private lemma one_sub_sq_pos {x : ℝ} (hx : x ∈ branch) : 0 < 1 - x ^ 2 := by
  change -1 < x ∧ x < 1 at hx
  have hp : 0 < (1 - x) * (1 + x) :=
    mul_pos (sub_pos.mpr hx.2) (by linarith [hx.1])
  nlinarith

private lemma hasDerivAt_of_eqOn_branch
    {f g : ℝ → ℝ} {x d : ℝ} (hx : x ∈ branch)
    (hfg : ∀ y ∈ branch, f y = g y) (hg : HasDerivAt g d x) :
    HasDerivAt f d x := by
  have hopen : IsOpen branch := by
    rw [branch]
    exact isOpen_Ioo
  apply hg.congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact hfg y hy

private lemma hasDerivAt_boundary₁ (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt boundary₁ (integrand x + 2 * residual₁ x) x := by
  have hx' : -1 < x ∧ x < 1 := by
    simpa [branch] using hx
  have ha := Real.hasDerivAt_arcsin (ne_of_gt hx'.1) (ne_of_lt hx'.2)
  have h := (hasDerivAt_id x).mul (ha.pow 2)
  convert h using 1 <;>
    simp [boundary₁, integrand, residual₁] <;> ring

private lemma hasDerivAt_root (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun t : ℝ => Real.sqrt (1 - t ^ 2))
      (-x / Real.sqrt (1 - x ^ 2)) x := by
  have hq : 0 < 1 - x ^ 2 := one_sub_sq_pos hx
  have hu : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      simp <;> ring
  have hs := (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hu
  have hsqrt : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  convert hs using 1 <;>
    field_simp [hsqrt] <;> ring

private lemma residual₂_eq_neg_residual₁ (x : ℝ) (hx : x ∈ branch) :
    residual₂ x = -residual₁ x := by
  change
    Real.arcsin x * deriv (fun t : ℝ => Real.sqrt (1 - t ^ 2)) x =
      -(x * Real.arcsin x / Real.sqrt (1 - x ^ 2))
  rw [(hasDerivAt_root x hx).deriv]
  ring

private lemma hasDerivAt_boundary₂ (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt boundary₂ (integrand x + 2) x := by
  have hq : 0 < 1 - x ^ 2 := one_sub_sq_pos hx
  have hsqrt : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hb := hasDerivAt_boundary₁ x hx
  have hr := hasDerivAt_root x hx
  have hx' : -1 < x ∧ x < 1 := by
    simpa [branch] using hx
  have ha := Real.hasDerivAt_arcsin (ne_of_gt hx'.1) (ne_of_lt hx'.2)
  have ht := ((hasDerivAt_const x (2 : ℝ)).mul hr).mul ha
  have h := hb.add ht
  convert h using 1 <;>
    simp [integrand, residual₁, hsqrt] <;>
    ring

private lemma eq_of_hasDerivAt_zero_on_branch
    {H : ℝ → ℝ} (hH : ∀ x ∈ branch, HasDerivAt H 0 x) :
    ∀ x ∈ branch, ∀ y ∈ branch, H x = H y := by
  have hordered :
      ∀ {a b : ℝ}, a ∈ branch → b ∈ branch → a < b → H a = H b := by
    intro a b ha hb hab
    have hcont : ContinuousOn H (Set.Icc a b) := by
      intro z hz
      have hzbranch : z ∈ branch := by
        change -1 < z ∧ z < 1
        change -1 < a ∧ a < 1 at ha
        change -1 < b ∧ b < 1 at hb
        exact ⟨by linarith [ha.1, hz.1], by linarith [hb.2, hz.2]⟩
      exact (hH z hzbranch).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ H (Set.Ioo a b) := by
      intro z hz
      have hzbranch : z ∈ branch := by
        change -1 < z ∧ z < 1
        change -1 < a ∧ a < 1 at ha
        change -1 < b ∧ b < 1 at hb
        exact ⟨by linarith [ha.1, hz.1], by linarith [hb.2, hz.2]⟩
      exact (hH z hzbranch).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hcderiv⟩ :=
      exists_deriv_eq_slope H hab hcont hdiff
    have hcbranch : c ∈ branch := by
      change -1 < c ∧ c < 1
      change -1 < a ∧ a < 1 at ha
      change -1 < b ∧ b < 1 at hb
      exact ⟨by linarith [ha.1, hc.1], by linarith [hb.2, hc.2]⟩
    have hdc : deriv H c = 0 := (hH c hcbranch).deriv
    rw [hdc] at hcderiv
    have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
    field_simp [hne] at hcderiv
    linarith
  intro x hx y hy
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact hordered hx hy hxy
  · exact congrArg H hxy
  · exact (hordered hy hx hxy).symm

private lemma eq_add_const_of_hasDerivAt_one
    {G : ℝ → ℝ} (hG : ∀ x ∈ branch, HasDerivAt G 1 x) :
    ∀ x ∈ branch, G x = x + G 0 := by
  have hzero :
      ∀ x ∈ branch, HasDerivAt (fun y => G y - y) 0 x := by
    intro x hx
    convert (hG x hx).sub (hasDerivAt_id x) using 1 <;> ring
  have h0 : (0 : ℝ) ∈ branch := by
    change (-1 : ℝ) < 0 ∧ 0 < 1
    constructor <;> linarith
  intro x hx
  have hc := eq_of_hasDerivAt_zero_on_branch hzero x hx 0 h0
  linarith

theorem gap1 :
    AntiderivativesOn integrand =
      ByPartsFamily boundary₁ (-2) residual₁ := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∃ G, (∀ x ∈ branch, HasDerivAt G (residual₁ x) x) ∧
        ∀ x ∈ branch, F x = boundary₁ x + (-2) * G x
  constructor
  · intro hF
    refine ⟨fun x => (boundary₁ x - F x) / 2, ?_, ?_⟩
    · intro x hx
      have h := ((hasDerivAt_boundary₁ x hx).sub (hF x hx)).div_const 2
      convert h using 1 <;> ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have h := (hasDerivAt_boundary₁ x hx).add
      ((hasDerivAt_const x (-2 : ℝ)).mul (hG x hx))
    have hc :
        HasDerivAt (fun y => boundary₁ y + (-2) * G y) (integrand x) x := by
      convert h using 1 <;> ring
    exact hasDerivAt_of_eqOn_branch hx hFG hc
theorem gap2 :
    ByPartsFamily boundary₁ (-2) residual₁ =
      ByPartsFamily boundary₁ 2 residual₂ := by
  apply Set.ext
  intro F
  change
    (∃ G, (∀ x ∈ branch, HasDerivAt G (residual₁ x) x) ∧
      ∀ x ∈ branch, F x = boundary₁ x + (-2) * G x) ↔
    ∃ G, (∀ x ∈ branch, HasDerivAt G (residual₂ x) x) ∧
      ∀ x ∈ branch, F x = boundary₁ x + 2 * G x
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨fun x => -G x, ?_, ?_⟩
    · intro x hx
      simpa only [residual₂_eq_neg_residual₁ x hx] using (hG x hx).neg
    · intro x hx
      simpa using hFG x hx
  · rintro ⟨G, hG, hFG⟩
    refine ⟨fun x => -G x, ?_, ?_⟩
    · intro x hx
      simpa only [residual₂_eq_neg_residual₁ x hx, neg_neg] using
        (hG x hx).neg
    · intro x hx
      simpa using hFG x hx
theorem gap3 :
    AntiderivativesOn integrand =
      ByPartsFamily boundary₁ 2 residual₂ := by
  exact gap1.trans gap2
theorem gap4 :
    AntiderivativesOn integrand =
      ByPartsFamily boundary₂ (-2) (fun _ => 1) := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∃ G, (∀ x ∈ branch, HasDerivAt G 1 x) ∧
        ∀ x ∈ branch, F x = boundary₂ x + (-2) * G x
  constructor
  · intro hF
    refine ⟨fun x => (boundary₂ x - F x) / 2, ?_, ?_⟩
    · intro x hx
      have h := ((hasDerivAt_boundary₂ x hx).sub (hF x hx)).div_const 2
      convert h using 1 <;> ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have h := (hasDerivAt_boundary₂ x hx).add
      ((hasDerivAt_const x (-2 : ℝ)).mul (hG x hx))
    have hc :
        HasDerivAt (fun y => boundary₂ y + (-2) * G y) (integrand x) x := by
      convert h using 1 <;> ring
    exact hasDerivAt_of_eqOn_branch hx hFG hc
theorem gap5 :
    ByPartsFamily boundary₂ (-2) (fun _ => 1) =
      PrimitiveFamily := by
  apply Set.ext
  intro F
  change
    (∃ G, (∀ x ∈ branch, HasDerivAt G 1 x) ∧
      ∀ x ∈ branch, F x = boundary₂ x + (-2) * G x) ↔
    ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨-2 * G 0, ?_⟩
    intro x hx
    have hGx := eq_add_const_of_hasDerivAt_one hG x hx
    rw [hFG x hx]
    unfold primitive
    linarith
  · rintro ⟨C, hFC⟩
    refine ⟨fun x => x - C / 2, ?_, ?_⟩
    · intro x hx
      convert (hasDerivAt_id x).sub (hasDerivAt_const x (C / 2)) using 1 <;>
        ring
    · intro x hx
      rw [hFC x hx]
      unfold primitive
      ring
theorem gap6 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  exact gap4.trans gap5

end
end ProofGap.Exercise1812
