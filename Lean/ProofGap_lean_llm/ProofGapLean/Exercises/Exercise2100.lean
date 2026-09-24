import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2100
noncomputable section

def U : Set ℝ := Set.Ioi 0
def f (x : ℝ) := (Real.log x / x) ^ 3
def primitive (x : ℝ) :=
  -1 / (2 * x ^ 2) *
    (Real.log x ^ 3 + 3 / 2 * Real.log x ^ 2 +
      3 / 2 * Real.log x + 3 / 4)
def Family (g : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (g x) x}
def Step1 := {F : ℝ → ℝ |
  ∃ G ∈ Family (fun x => Real.log x ^ 3 * deriv (fun y => 1 / y ^ 2) x),
  ∃ C, ∀ x ∈ U, F x = -G x / 2 + C}
def Step2 := {F : ℝ → ℝ |
  ∃ G ∈ Family (fun x => Real.log x ^ 2 / x ^ 3), ∃ C, ∀ x ∈ U,
  F x = -Real.log x ^ 3 / (2 * x ^ 2) + 3 / 2 * G x + C}
def Step3 := {F : ℝ → ℝ |
  ∃ G ∈ Family (fun x => Real.log x ^ 2 * deriv (fun y => 1 / y ^ 2) x),
  ∃ C, ∀ x ∈ U,
  F x = -Real.log x ^ 3 / (2 * x ^ 2) - 3 / 4 * G x + C}
def Step5 := {F : ℝ → ℝ |
  ∃ G ∈ Family (fun x => Real.log x / x ^ 3), ∃ C, ∀ x ∈ U,
  F x = -Real.log x ^ 3 / (2 * x ^ 2) -
    3 * Real.log x ^ 2 / (4 * x ^ 2) + 3 / 2 * G x + C}
def Step6 := {F : ℝ → ℝ |
  ∃ G ∈ Family (fun x => Real.log x * deriv (fun y => 1 / y ^ 2) x),
  ∃ C, ∀ x ∈ U,
  F x = -Real.log x ^ 3 / (2 * x ^ 2) -
    3 * Real.log x ^ 2 / (4 * x ^ 2) - 3 / 4 * G x + C}
def Step8 := {F : ℝ → ℝ |
  ∃ G ∈ Family (fun x => 1 / x ^ 3), ∃ C, ∀ x ∈ U,
  F x = -Real.log x ^ 3 / (2 * x ^ 2) -
    3 * Real.log x ^ 2 / (4 * x ^ 2) -
    3 * Real.log x / (4 * x ^ 2) + 3 / 4 * G x + C}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}

private theorem hasDerivAt_inv_sq {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 / y ^ 2) (-2 / x ^ 3) x := by
  convert (((hasDerivAt_id x).pow 2).inv (pow_ne_zero 2 hx)) using 1
  · funext y
    simp [div_eq_mul_inv]
  · field_simp [hx]
    <;> simp only [Pi.pow_apply, id_eq]
    <;> ring_nf

private theorem family_eq_affine
    {g h a : ℝ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (ha : ∀ x ∈ U, HasDerivAt a (g x - c * h x) x) :
    Family g = {F : ℝ → ℝ |
      ∃ G ∈ Family h, ∃ C, ∀ x ∈ U, F x = a x + c * G x + C} := by
  ext F
  constructor
  · intro hF
    let G : ℝ → ℝ := fun y => c⁻¹ * (F y - a y)
    have hG : G ∈ Family h := by
      intro x hx
      have hd := ((hF x hx).sub (ha x hx)).const_mul c⁻¹
      have hv : c⁻¹ * (g x - (g x - c * h x)) = h x := by
        field_simp [hc] <;> ring
      simpa only [G, hv] using hd
    refine ⟨G, hG, 0, ?_⟩
    intro x hx
    dsimp [G]
    field_simp [hc] <;> ring
  · rintro ⟨G, hG, C, hEq⟩
    intro x hx
    have hd : HasDerivAt (fun y => a y + c * G y) (g x) x := by
      convert (ha x hx).add ((hG x hx).const_mul c) using 1 <;> ring
    have hdC := hd.add_const C
    change 0 < x at hx
    have hlocal :
        (fun y => a y + c * G y + C) =ᶠ[nhds x] F := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      rw [hEq y (show y ∈ U by exact hy)]
    exact hdC.congr_of_eventuallyEq hlocal.symm

private theorem family_eq_translates_of_deriv
    {g p : ℝ → ℝ}
    (hp : ∀ x ∈ U, HasDerivAt p (g x) x) :
    Family g = Translates p := by
  ext F
  constructor
  · intro hF
    let q : ℝ → ℝ := fun y => F y - p y
    have hdiff : DifferentiableOn ℝ q U := by
      intro x hx
      exact ((hF x hx).sub (hp x hx)).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ U, deriv q x = 0 := by
      intro x hx
      have hd := ((hF x hx).sub (hp x hx)).deriv
      simpa only [q, sub_self] using hd
    have h1 : (1 : ℝ) ∈ U := by
      change (0 : ℝ) < 1
      exact zero_lt_one
    refine ⟨q 1, ?_⟩
    intro x hx
    have hxy : q x = q 1 :=
      isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hzero hx h1
    dsimp [q] at hxy ⊢
    linarith
  · rintro ⟨C, hEq⟩
    intro x hx
    have hd := (hp x hx).add_const C
    change 0 < x at hx
    have hlocal : (fun y => p y + C) =ᶠ[nhds x] F := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      rw [hEq y (show y ∈ U by exact hy)]
    exact hd.congr_of_eventuallyEq hlocal.symm

theorem gap1 : Family f = Step1 := by
  have he := family_eq_affine
    (g := f)
    (h := fun x => Real.log x ^ 3 * deriv (fun y => 1 / y ^ 2) x)
    (a := fun _ => 0)
    (c := -(1 / 2 : ℝ))
    (by norm_num)
    (by
      intro x hx
      change 0 < x at hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hi2 := hasDerivAt_inv_sq hx0
      have hdi : deriv (fun y : ℝ => 1 / y ^ 2) x = -2 / x ^ 3 := hi2.deriv
      have hz :
          f x - (-(1 / 2 : ℝ)) *
            (Real.log x ^ 3 * deriv (fun y : ℝ => 1 / y ^ 2) x) = 0 := by
        rw [hdi]
        unfold f
        field_simp [hx0] <;> ring_nf
      simpa only [hz] using (hasDerivAt_const (x := x) (c := (0 : ℝ))))
  rw [he]
  unfold Step1
  ext F
  constructor
  · rintro ⟨G, hG, C, hFC⟩
    refine ⟨G, hG, C, ?_⟩
    intro x hx
    have h := hFC x hx
    dsimp at h ⊢
    linarith
  · rintro ⟨G, hG, C, hFC⟩
    refine ⟨G, hG, C, ?_⟩
    intro x hx
    have h := hFC x hx
    dsimp at h ⊢
    linarith
theorem gap2 : Step1 = Step2 := by
  rw [← gap1]
  have he := family_eq_affine
    (g := f)
    (h := fun x => Real.log x ^ 2 / x ^ 3)
    (a := fun x => -Real.log x ^ 3 / (2 * x ^ 2))
    (c := (3 / 2 : ℝ))
    (by norm_num)
    (by
      intro x hx
      change 0 < x at hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hl := Real.hasDerivAt_log hx0
      have hi2 := hasDerivAt_inv_sq hx0
      convert ((hl.pow 3).mul hi2).const_mul (-(1 / 2 : ℝ)) using 1
      · funext y
        simp [div_eq_mul_inv] <;> ring
      · unfold f
        simp only [Pi.pow_apply]
        field_simp [hx0] <;> ring_nf)
  simpa [Step2] using he
theorem gap3 : Step2 = Step3 := by
  rw [← gap2, ← gap1]
  have he := family_eq_affine
    (g := f)
    (h := fun x => Real.log x ^ 2 * deriv (fun y => 1 / y ^ 2) x)
    (a := fun x => -Real.log x ^ 3 / (2 * x ^ 2))
    (c := -(3 / 4 : ℝ))
    (by norm_num)
    (by
      intro x hx
      change 0 < x at hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hl := Real.hasDerivAt_log hx0
      have hi2 := hasDerivAt_inv_sq hx0
      have hdi : deriv (fun y : ℝ => 1 / y ^ 2) x = -2 / x ^ 3 := hi2.deriv
      convert ((hl.pow 3).mul hi2).const_mul (-(1 / 2 : ℝ)) using 1
      · funext y
        simp [div_eq_mul_inv] <;> ring
      · simp only [Pi.pow_apply]
        rw [hdi]
        unfold f
        field_simp [hx0] <;> ring_nf)
  simpa [Step3] using he
theorem gap4 : Family f = Step3 := by
  exact gap1.trans (gap2.trans gap3)
theorem gap5 : Family f = Step5 := by
  have he := family_eq_affine
    (g := f)
    (h := fun x => Real.log x / x ^ 3)
    (a := fun x =>
      -Real.log x ^ 3 / (2 * x ^ 2) -
        3 * Real.log x ^ 2 / (4 * x ^ 2))
    (c := (3 / 2 : ℝ))
    (by norm_num)
    (by
      intro x hx
      change 0 < x at hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hl := Real.hasDerivAt_log hx0
      have hi2 := hasDerivAt_inv_sq hx0
      convert
        (((hl.pow 3).mul hi2).const_mul (-(1 / 2 : ℝ))).add
          (((hl.pow 2).mul hi2).const_mul (-(3 / 4 : ℝ))) using 1
      · funext y
        simp [div_eq_mul_inv] <;> ring
      · unfold f
        simp only [Pi.pow_apply]
        field_simp [hx0] <;> ring_nf)
  simpa [Step5] using he
theorem gap6 : Step5 = Step6 := by
  rw [← gap5]
  have he := family_eq_affine
    (g := f)
    (h := fun x => Real.log x * deriv (fun y => 1 / y ^ 2) x)
    (a := fun x =>
      -Real.log x ^ 3 / (2 * x ^ 2) -
        3 * Real.log x ^ 2 / (4 * x ^ 2))
    (c := -(3 / 4 : ℝ))
    (by norm_num)
    (by
      intro x hx
      change 0 < x at hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hl := Real.hasDerivAt_log hx0
      have hi2 := hasDerivAt_inv_sq hx0
      have hdi : deriv (fun y : ℝ => 1 / y ^ 2) x = -2 / x ^ 3 := hi2.deriv
      convert
        (((hl.pow 3).mul hi2).const_mul (-(1 / 2 : ℝ))).add
          (((hl.pow 2).mul hi2).const_mul (-(3 / 4 : ℝ))) using 1
      · funext y
        simp [div_eq_mul_inv] <;> ring
      · simp only [Pi.pow_apply]
        rw [hdi]
        unfold f
        field_simp [hx0] <;> ring_nf)
  simpa [Step6] using he
theorem gap7 : Family f = Step6 := by
  exact gap5.trans gap6
theorem gap8 : Family f = Step8 := by
  have he := family_eq_affine
    (g := f)
    (h := fun x => 1 / x ^ 3)
    (a := fun x =>
      -Real.log x ^ 3 / (2 * x ^ 2) -
        3 * Real.log x ^ 2 / (4 * x ^ 2) -
        3 * Real.log x / (4 * x ^ 2))
    (c := (3 / 4 : ℝ))
    (by norm_num)
    (by
      intro x hx
      change 0 < x at hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hl := Real.hasDerivAt_log hx0
      have hi2 := hasDerivAt_inv_sq hx0
      convert
        ((((hl.pow 3).mul hi2).const_mul (-(1 / 2 : ℝ))).add
          (((hl.pow 2).mul hi2).const_mul (-(3 / 4 : ℝ)))).add
          ((hl.mul hi2).const_mul (-(3 / 4 : ℝ))) using 1
      · funext y
        simp [div_eq_mul_inv] <;> ring
      · unfold f
        simp only [Pi.pow_apply]
        field_simp [hx0] <;> ring_nf)
  simpa [Step8] using he
theorem gap9 : Step8 = Translates primitive := by
  apply gap8.symm.trans
  apply family_eq_translates_of_deriv
  intro x hx
  change 0 < x at hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hl := Real.hasDerivAt_log hx0
  have hi2 := hasDerivAt_inv_sq hx0
  convert
    (((((hl.pow 3).mul hi2).const_mul (-(1 / 2 : ℝ))).add
      (((hl.pow 2).mul hi2).const_mul (-(3 / 4 : ℝ)))).add
      ((hl.mul hi2).const_mul (-(3 / 4 : ℝ)))).add
      (hi2.const_mul (-(3 / 8 : ℝ))) using 1
  · funext y
    unfold primitive
    simp [div_eq_mul_inv] <;> ring
  · unfold f
    simp only [Pi.pow_apply]
    field_simp [hx0] <;> ring_nf
theorem gap10 : Family f = Translates primitive := by
  exact gap8.trans gap9

end
end ProofGap.Exercise2100
