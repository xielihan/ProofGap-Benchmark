import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise2002

noncomputable section

def branch : Set ℝ := {x | Real.sin x ≠ 0 ∧ Real.cos x ≠ 0}
def cot (x : ℝ) := Real.cos x / Real.sin x
def originalIntegrand (x : ℝ) :=
  1 / (Real.sin x ^ 3 * Real.cos x ^ 5)
def identityIntegrand (x : ℝ) :=
  (Real.sin x ^ 2 + Real.cos x ^ 2) /
    (Real.sin x ^ 3 * Real.cos x ^ 5)
def a₁ (x : ℝ) := 1 / (Real.sin x * Real.cos x ^ 5)
def a₂ (x : ℝ) := 1 / (Real.sin x ^ 3 * Real.cos x ^ 3)
def b₁ (x : ℝ) :=
  (Real.sin x ^ 2 + Real.cos x ^ 2) /
    (Real.sin x * Real.cos x ^ 5)
def b₂ (x : ℝ) :=
  (Real.sin x ^ 2 + Real.cos x ^ 2) /
    (Real.sin x ^ 3 * Real.cos x ^ 3)
def c₁ (x : ℝ) := Real.sin x / Real.cos x ^ 5
def c₂ (x : ℝ) := 1 / (Real.sin x * Real.cos x ^ 3)
def c₃ (x : ℝ) := 1 / (Real.sin x ^ 3 * Real.cos x)
def d₁ (x : ℝ) := deriv Real.cos x / Real.cos x ^ 5
def d₂ (x : ℝ) := Real.sin x / Real.cos x ^ 3
def d₃ (x : ℝ) := 1 / (Real.sin x * Real.cos x)
def d₄ (x : ℝ) := Real.cos x / Real.sin x ^ 3
def e₁ (x : ℝ) := deriv Real.cos x / Real.cos x ^ 3
def e₂ (x : ℝ) := deriv Real.tan x / Real.tan x
def e₃ (x : ℝ) := deriv Real.sin x / Real.sin x ^ 3
def primitive₁ (x : ℝ) :=
  1 / (4 * Real.cos x ^ 4) + 1 / Real.cos x ^ 2 +
    3 * Real.log |Real.tan x| - 1 / (2 * Real.sin x ^ 2)
def primitive₂ (x : ℝ) :=
  1 / 4 * Real.tan x ^ 4 + 3 / 2 * Real.tan x ^ 2 -
    1 / 2 * cot x ^ 2 + 3 * Real.log |Real.tan x|
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def TwoTermFamily (f g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives f, ∃ H ∈ Antiderivatives g,
    ∀ x ∈ branch, F x = G x + H x}
def ThreeTermFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives c₁,
    ∃ H ∈ Antiderivatives c₂,
    ∃ K ∈ Antiderivatives c₃,
      ∀ x ∈ branch, F x = G x + 2 * H x + K x}
def FourTermFamily : Set (ℝ → ℝ) :=
  {F | ∃ G₁ ∈ Antiderivatives d₁,
    ∃ G₂ ∈ Antiderivatives d₂,
    ∃ G₃ ∈ Antiderivatives d₃,
    ∃ G₄ ∈ Antiderivatives d₄,
      ∀ x ∈ branch,
        F x = -G₁ x + 2 * G₂ x + 3 * G₃ x + G₄ x}
def BoundaryFamily : Set (ℝ → ℝ) :=
  {F | ∃ G₁ ∈ Antiderivatives e₁,
    ∃ G₂ ∈ Antiderivatives e₂,
    ∃ G₃ ∈ Antiderivatives e₃,
      ∀ x ∈ branch,
        F x =
          1 / (4 * Real.cos x ^ 4) - 2 * G₁ x + 3 * G₂ x + G₃ x}
def ComponentwisePrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ K : ℝ → ℝ,
    (∀ x ∈ branch, F x = p x + K x) ∧
    (∀ x ∈ branch, HasDerivAt K 0 x)}

private def q (x : ℝ) := 1 / (4 * Real.cos x ^ 4)
private def r (x : ℝ) := 1 / (2 * Real.cos x ^ 2)
private def l (x : ℝ) := Real.log |Real.tan x|
private def t (x : ℝ) := -1 / (2 * Real.sin x ^ 2)

private lemma hasDerivAt_of_eq_on_branch
    {f g : ℝ → ℝ} {f' x : ℝ} (hx : x ∈ branch)
    (hfg : ∀ y ∈ branch, f y = g y)
    (hg : HasDerivAt g f' x) : HasDerivAt f f' x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards
    [Real.continuous_sin.continuousAt.eventually_ne hx.1,
      Real.continuous_cos.continuousAt.eventually_ne hx.2] with y hs hc
  exact hfg y ⟨hs, hc⟩

private lemma tan_ne_zero (x : ℝ) (hx : x ∈ branch) :
    Real.tan x ≠ 0 := by
  rw [Real.tan_eq_sin_div_cos]
  exact div_ne_zero hx.1 hx.2

private lemma hasDerivAt_tan_local (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt Real.tan (1 / Real.cos x ^ 2) x := by
  have h := (Real.hasDerivAt_sin x).div (Real.hasDerivAt_cos x) hx.2
  convert h using 1
  · funext y
    rw [Real.tan_eq_sin_div_cos]
    rfl
  · field_simp [hx.2]
    nlinarith [Real.sin_sq_add_cos_sq x]

private lemma hasDerivAt_q (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt q (c₁ x) x := by
  have hc := Real.hasDerivAt_cos x
  have hden :
      HasDerivAt (fun y : ℝ => 4 * Real.cos y ^ 4)
        (4 * (4 * Real.cos x ^ 3 * (-Real.sin x))) x := by
    convert (hc.pow 4).const_mul 4 using 1 <;> ring
  unfold q c₁
  apply ((hasDerivAt_const x (1 : ℝ)).div hden
    (mul_ne_zero (by norm_num) (pow_ne_zero 4 hx.2))).congr_deriv
  field_simp [hx.2]
  ring

private lemma hasDerivAt_r (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt r (d₂ x) x := by
  have hc := Real.hasDerivAt_cos x
  have hden :
      HasDerivAt (fun y : ℝ => 2 * Real.cos y ^ 2)
        (2 * (2 * Real.cos x * (-Real.sin x))) x := by
    convert (hc.pow 2).const_mul 2 using 1 <;> ring
  unfold r d₂
  apply ((hasDerivAt_const x (1 : ℝ)).div hden
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx.2))).congr_deriv
  field_simp [hx.2]
  ring

private lemma hasDerivAt_l (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt l (d₃ x) x := by
  have htan := hasDerivAt_tan_local x hx
  have hlog := (Real.hasDerivAt_log (tan_ne_zero x hx)).comp x htan
  have hlogabs :
      HasDerivAt (fun y => Real.log |Real.tan y|)
        ((Real.tan x)⁻¹ * (1 / Real.cos x ^ 2)) x := by
    simpa only [Function.comp_apply, Real.log_abs] using hlog
  unfold l d₃
  apply hlogabs.congr_deriv
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hx.1, hx.2]

private lemma hasDerivAt_t (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt t (d₄ x) x := by
  have hs := Real.hasDerivAt_sin x
  have hden :
      HasDerivAt (fun y : ℝ => 2 * Real.sin y ^ 2)
        (2 * (2 * Real.sin x * Real.cos x)) x := by
    convert (hs.pow 2).const_mul 2 using 1 <;> ring
  unfold t d₄
  apply ((hasDerivAt_const x (-1 : ℝ)).div hden
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx.1))).congr_deriv
  field_simp [hx.1]
  ring

private lemma hasDerivAt_c₂_primitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y => r y + l y) (c₂ x) x := by
  apply ((hasDerivAt_r x hx).add (hasDerivAt_l x hx)).congr_deriv
  unfold c₂ d₂ d₃
  field_simp [hx.1, hx.2]
  nlinarith [Real.sin_sq_add_cos_sq x]

private lemma hasDerivAt_a₁_primitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y => q y + r y + l y) (a₁ x) x := by
  have h := (hasDerivAt_q x hx).add
    ((hasDerivAt_r x hx).add (hasDerivAt_l x hx))
  simpa only [Pi.add_apply, add_assoc] using h.congr_deriv (by
    unfold a₁ c₁ d₂ d₃
    field_simp [hx.1, hx.2]
    nlinarith [Real.sin_sq_add_cos_sq x])

private lemma original_eq_identity (x : ℝ) :
    originalIntegrand x = identityIntegrand x := by
  unfold originalIntegrand identityIntegrand
  rw [Real.sin_sq_add_cos_sq]

private lemma identity_eq_a_sum (x : ℝ) (hx : x ∈ branch) :
    identityIntegrand x = a₁ x + a₂ x := by
  unfold identityIntegrand a₁ a₂
  field_simp [hx.1, hx.2]

private lemma b₁_eq_c_sum (x : ℝ) (hx : x ∈ branch) :
    b₁ x = c₁ x + c₂ x := by
  unfold b₁ c₁ c₂
  field_simp [hx.1, hx.2]

private lemma b₂_eq_c_sum (x : ℝ) (hx : x ∈ branch) :
    b₂ x = c₂ x + c₃ x := by
  unfold b₂ c₂ c₃
  field_simp [hx.1, hx.2]

private lemma c₁_eq_neg_d₁ (x : ℝ) :
    c₁ x = -d₁ x := by
  unfold c₁ d₁
  rw [(Real.hasDerivAt_cos x).deriv]
  ring

private lemma c₂_eq_d_sum (x : ℝ) (hx : x ∈ branch) :
    c₂ x = d₂ x + d₃ x := by
  unfold c₂ d₂ d₃
  field_simp [hx.1, hx.2]
  nlinarith [Real.sin_sq_add_cos_sq x]

private lemma c₃_eq_d_sum (x : ℝ) (hx : x ∈ branch) :
    c₃ x = d₃ x + d₄ x := by
  unfold c₃ d₃ d₄
  field_simp [hx.1, hx.2]
  nlinarith [Real.sin_sq_add_cos_sq x]

private lemma e₁_eq_neg_d₂ (x : ℝ) :
    e₁ x = -d₂ x := by
  unfold e₁ d₂
  rw [(Real.hasDerivAt_cos x).deriv]
  ring

private lemma e₂_eq_d₃ (x : ℝ) (hx : x ∈ branch) :
    e₂ x = d₃ x := by
  unfold e₂ d₃
  rw [(hasDerivAt_tan_local x hx).deriv, Real.tan_eq_sin_div_cos]
  field_simp [hx.1, hx.2]

private lemma e₃_eq_d₄ (x : ℝ) :
    e₃ x = d₄ x := by
  unfold e₃ d₄
  rw [(Real.hasDerivAt_sin x).deriv]

theorem gap1 :
    Antiderivatives originalIntegrand =
      Antiderivatives identityIntegrand := by
  ext F
  constructor <;> intro hF <;> intro x hx
  · rw [← original_eq_identity x]
    exact hF x hx
  · rw [original_eq_identity x]
    exact hF x hx
theorem gap2 :
    Antiderivatives identityIntegrand =
      TwoTermFamily a₁ a₂ := by
  ext F
  constructor
  · intro hF
    refine ⟨fun y => q y + r y + l y, ?_,
      fun y => F y - (q y + r y + l y), ?_, ?_⟩
    · exact hasDerivAt_a₁_primitive
    · intro x hx
      apply ((hF x hx).sub (hasDerivAt_a₁_primitive x hx)).congr_deriv
      rw [identity_eq_a_sum x hx]
      ring
    · intro x hx
      ring
  · rintro ⟨G, hG, H, hH, hFG⟩
    intro x hx
    apply hasDerivAt_of_eq_on_branch
      (f := F) (g := fun y => G y + H y) hx hFG
    apply ((hG x hx).add (hH x hx)).congr_deriv
    rw [identity_eq_a_sum x hx]
theorem gap3 :
    Antiderivatives originalIntegrand =
      TwoTermFamily a₁ a₂ := by
  rw [gap1, gap2]
theorem gap4 :
    Antiderivatives originalIntegrand =
      TwoTermFamily b₁ b₂ := by
  rw [gap3]
  ext F
  constructor
  · rintro ⟨G, hG, H, hH, hFG⟩
    refine ⟨G, ?_, H, ?_, hFG⟩
    · intro x hx
      have hunit := Real.sin_sq_add_cos_sq x
      have heq : b₁ x = a₁ x := by
        unfold b₁ a₁
        rw [hunit]
      simpa only [heq] using hG x hx
    · intro x hx
      have hunit := Real.sin_sq_add_cos_sq x
      have heq : b₂ x = a₂ x := by
        unfold b₂ a₂
        rw [hunit]
      simpa only [heq] using hH x hx
  · rintro ⟨G, hG, H, hH, hFG⟩
    refine ⟨G, ?_, H, ?_, hFG⟩
    · intro x hx
      have hunit := Real.sin_sq_add_cos_sq x
      have heq : b₁ x = a₁ x := by
        unfold b₁ a₁
        rw [hunit]
      simpa only [heq] using hG x hx
    · intro x hx
      have hunit := Real.sin_sq_add_cos_sq x
      have heq : b₂ x = a₂ x := by
        unfold b₂ a₂
        rw [hunit]
      simpa only [heq] using hH x hx
theorem gap5 :
    TwoTermFamily b₁ b₂ = ThreeTermFamily := by
  ext F
  constructor
  · rintro ⟨G, hG, H, hH, hFG⟩
    let B : ℝ → ℝ := fun y => r y + l y
    refine ⟨fun y => G y - B y, ?_, B, ?_,
      fun y => H y - B y, ?_, ?_⟩
    · intro x hx
      apply ((hG x hx).sub (hasDerivAt_c₂_primitive x hx)).congr_deriv
      rw [b₁_eq_c_sum x hx]
      ring
    · exact hasDerivAt_c₂_primitive
    · intro x hx
      apply ((hH x hx).sub (hasDerivAt_c₂_primitive x hx)).congr_deriv
      rw [b₂_eq_c_sum x hx]
      ring
    · intro x hx
      rw [hFG x hx]
      ring
  · rintro ⟨G, hG, H, hH, K, hK, hF⟩
    refine ⟨fun y => G y + H y, ?_,
      fun y => H y + K y, ?_, ?_⟩
    · intro x hx
      apply ((hG x hx).add (hH x hx)).congr_deriv
      rw [b₁_eq_c_sum x hx]
    · intro x hx
      apply ((hH x hx).add (hK x hx)).congr_deriv
      rw [b₂_eq_c_sum x hx]
    · intro x hx
      rw [hF x hx]
      ring
theorem gap6 :
    Antiderivatives originalIntegrand = ThreeTermFamily := by
  rw [gap4, gap5]
theorem gap7 :
    Antiderivatives originalIntegrand = FourTermFamily := by
  rw [gap6]
  ext F
  constructor
  · rintro ⟨G, hG, H, hH, K, hK, hF⟩
    refine ⟨fun y => -G y, ?_,
      fun y => H y - l y, ?_, l, ?_,
      fun y => K y - l y, ?_, ?_⟩
    · intro x hx
      apply (hG x hx).neg.congr_deriv
      rw [c₁_eq_neg_d₁]
      ring
    · intro x hx
      apply ((hH x hx).sub (hasDerivAt_l x hx)).congr_deriv
      rw [c₂_eq_d_sum x hx]
      ring
    · exact hasDerivAt_l
    · intro x hx
      apply ((hK x hx).sub (hasDerivAt_l x hx)).congr_deriv
      rw [c₃_eq_d_sum x hx]
      ring
    · intro x hx
      rw [hF x hx]
      ring
  · rintro ⟨G₁, hG₁, G₂, hG₂, G₃, hG₃, G₄, hG₄, hF⟩
    refine ⟨fun y => -G₁ y, ?_,
      fun y => G₂ y + G₃ y, ?_,
      fun y => G₃ y + G₄ y, ?_, ?_⟩
    · intro x hx
      apply (hG₁ x hx).neg.congr_deriv
      rw [c₁_eq_neg_d₁]
    · intro x hx
      apply ((hG₂ x hx).add (hG₃ x hx)).congr_deriv
      rw [c₂_eq_d_sum x hx]
    · intro x hx
      apply ((hG₃ x hx).add (hG₄ x hx)).congr_deriv
      rw [c₃_eq_d_sum x hx]
    · intro x hx
      rw [hF x hx]
      ring
theorem gap8 :
    Antiderivatives originalIntegrand = BoundaryFamily := by
  rw [gap7]
  ext F
  constructor
  · rintro ⟨G₁, hG₁, G₂, hG₂, G₃, hG₃, G₄, hG₄, hF⟩
    refine ⟨fun y => (q y + G₁ y - 2 * G₂ y) / 2, ?_,
      G₃, ?_, G₄, ?_, ?_⟩
    · intro x hx
      have h := ((hasDerivAt_q x hx).add (hG₁ x hx)).sub
        ((hG₂ x hx).const_mul 2)
      apply (h.div_const 2).congr_deriv
      rw [c₁_eq_neg_d₁, e₁_eq_neg_d₂]
      ring
    · intro x hx
      apply (hG₃ x hx).congr_deriv
      rw [e₂_eq_d₃ x hx]
    · intro x hx
      apply (hG₄ x hx).congr_deriv
      rw [e₃_eq_d₄]
    · intro x hx
      rw [hF x hx]
      unfold q
      ring
  · rintro ⟨G₁, hG₁, G₂, hG₂, G₃, hG₃, hF⟩
    refine ⟨fun y => -q y, ?_, fun y => -G₁ y, ?_,
      G₂, ?_, G₃, ?_, ?_⟩
    · intro x hx
      apply (hasDerivAt_q x hx).neg.congr_deriv
      rw [c₁_eq_neg_d₁]
      ring
    · intro x hx
      apply (hG₁ x hx).neg.congr_deriv
      rw [e₁_eq_neg_d₂]
      ring
    · intro x hx
      apply (hG₂ x hx).congr_deriv
      rw [e₂_eq_d₃ x hx]
    · intro x hx
      apply (hG₃ x hx).congr_deriv
      rw [e₃_eq_d₄]
    · intro x hx
      rw [hF x hx]
      unfold q
      ring

private lemma hasDerivAt_primitive₁ (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive₁ (originalIntegrand x) x := by
  have h := (((hasDerivAt_q x hx).add
    ((hasDerivAt_r x hx).const_mul 2)).add
    ((hasDerivAt_l x hx).const_mul 3)).add (hasDerivAt_t x hx)
  convert h using 1
  · funext y
    simp only [Pi.add_apply]
    unfold primitive₁ q r l t
    ring
  · calc
      originalIntegrand x = b₁ x + b₂ x := by
        unfold b₁ b₂ originalIntegrand
        field_simp [hx.1, hx.2]
        nlinarith [Real.sin_sq_add_cos_sq x]
      _ = c₁ x + 2 * c₂ x + c₃ x := by
        rw [b₁_eq_c_sum x hx, b₂_eq_c_sum x hx]
        ring
      _ = c₁ x + 2 * d₂ x + 3 * d₃ x + d₄ x := by
        rw [c₂_eq_d_sum x hx, c₃_eq_d_sum x hx]
        ring
theorem gap9 :
    BoundaryFamily = ComponentwisePrimitiveFamily primitive₁ := by
  rw [← gap8]
  ext F
  constructor
  · intro hF
    refine ⟨fun y => F y - primitive₁ y, ?_, ?_⟩
    · intro x hx
      ring
    · intro x hx
      apply ((hF x hx).sub (hasDerivAt_primitive₁ x hx)).congr_deriv
      ring
  · rintro ⟨K, hFK, hK⟩
    intro x hx
    apply hasDerivAt_of_eq_on_branch
      (f := F) (g := fun y => primitive₁ y + K y) hx hFK
    apply ((hasDerivAt_primitive₁ x hx).add (hK x hx)).congr_deriv
    ring
theorem gap10 :
    Antiderivatives originalIntegrand =
      ComponentwisePrimitiveFamily primitive₁ := by
  rw [gap8, gap9]

private lemma primitive₁_eq_primitive₂_add_const
    (x : ℝ) (hx : x ∈ branch) :
    primitive₁ x = primitive₂ x + (3 / 4 : ℝ) := by
  unfold primitive₁ primitive₂ cot
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hx.1, hx.2]
  linear_combination
    -(2 * Real.sin x ^ 4 +
      10 * Real.sin x ^ 2 * Real.cos x ^ 2 -
      4 * Real.cos x ^ 4 + 2 * Real.sin x ^ 2) *
      (Real.sin_sq_add_cos_sq x)
theorem gap11 :
    Antiderivatives originalIntegrand =
      ComponentwisePrimitiveFamily primitive₂ := by
  rw [gap10]
  ext F
  constructor
  · rintro ⟨K, hFK, hK⟩
    refine ⟨fun y => K y + (3 / 4 : ℝ), ?_, ?_⟩
    · intro x hx
      rw [hFK x hx, primitive₁_eq_primitive₂_add_const x hx]
      ring
    · intro x hx
      simpa using (hK x hx).add_const (3 / 4 : ℝ)
  · rintro ⟨K, hFK, hK⟩
    refine ⟨fun y => K y - (3 / 4 : ℝ), ?_, ?_⟩
    · intro x hx
      rw [hFK x hx, primitive₁_eq_primitive₂_add_const x hx]
      ring
    · intro x hx
      simpa using (hK x hx).sub_const (3 / 4 : ℝ)

end
end ProofGap.Exercise2002
