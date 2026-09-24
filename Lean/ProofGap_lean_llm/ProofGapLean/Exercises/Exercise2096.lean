import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2096
noncomputable section

def f (x : ℝ) := x * Real.exp x / (x + 1) ^ 2
def primitive (x : ℝ) := Real.exp x / (x + 1)
def Family (U : Set ℝ) (g : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (g x) x}
def Step1 (U : Set ℝ) := {F : ℝ → ℝ |
  ∃ G ∈ Family U (fun x => x * Real.exp x * deriv (fun y => 1 / (y + 1)) x),
  ∃ C, ∀ x ∈ U, F x = -G x + C}
def Step2 (U : Set ℝ) := {F : ℝ → ℝ |
  ∃ G ∈ Family U Real.exp, ∃ C, ∀ x ∈ U,
    F x = -x * Real.exp x / (x + 1) + G x + C}
def Expanded (U : Set ℝ) := {F : ℝ → ℝ | ∃ C, ∀ x ∈ U,
  F x = -x * Real.exp x / (x + 1) + Real.exp x + C}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}
def Regular (U : Set ℝ) :=
  IsOpen U ∧ IsPreconnected U ∧ ∀ x ∈ U, x ≠ -1

private theorem reciprocal_hasDerivAt (x : ℝ) (hx : x ≠ -1) :
    HasDerivAt (fun y : ℝ => 1 / (y + 1)) (-1 / (x + 1) ^ 2) x := by
  have hden : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  convert (hasDerivAt_const x (1 : ℝ)).div
    ((hasDerivAt_id x).add_const 1) hden using 1
  field_simp [hden] <;> simp only [id_eq, Pi.mul_apply] <;> ring_nf

private theorem reciprocal_integrand_eq_neg_f (x : ℝ) (hx : x ≠ -1) :
    x * Real.exp x * deriv (fun y : ℝ => 1 / (y + 1)) x = -f x := by
  rw [(reciprocal_hasDerivAt x hx).deriv]
  unfold f
  ring

private theorem quotient_term_hasDerivAt (x : ℝ) (hx : x ≠ -1) :
    HasDerivAt (fun y : ℝ => y * Real.exp y / (y + 1))
      (Real.exp x - f x) x := by
  have hden : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  unfold f
  convert ((hasDerivAt_id x).mul (Real.hasDerivAt_exp x)).div
    ((hasDerivAt_id x).add_const 1) hden using 1
  field_simp [hden] <;> simp only [id_eq, Pi.mul_apply] <;> ring_nf

private theorem hasDerivAt_of_eqOn_open
    {U : Set ℝ} (hOpen : IsOpen U) {F H : ℝ → ℝ} {d x : ℝ}
    (hx : x ∈ U) (hEq : ∀ y ∈ U, F y = H y)
    (hH : HasDerivAt H d x) : HasDerivAt F d x := by
  apply hH.congr_of_eventuallyEq
  exact Filter.mem_of_superset (hOpen.mem_nhds hx)
    (fun y hy => hEq y hy)

private theorem family_exp_is_translate
    (U : Set ℝ) (hOpen : IsOpen U) (hConn : IsPreconnected U)
    {G : ℝ → ℝ} (hG : G ∈ Family U Real.exp) :
    ∃ C, ∀ x ∈ U, G x = Real.exp x + C := by
  change ∀ x ∈ U, HasDerivAt G (Real.exp x) x at hG
  by_cases hne : U.Nonempty
  · rcases hne with ⟨x₀, hx₀⟩
    have hdiff : DifferentiableOn ℝ (fun y : ℝ => G y - Real.exp y) U := by
      intro y hy
      exact ((hG y hy).sub (Real.hasDerivAt_exp y)).differentiableAt.differentiableWithinAt
    have hzero : ∀ y ∈ U, deriv (fun z : ℝ => G z - Real.exp z) y = 0 := by
      intro y hy
      simpa only [sub_self] using
        ((hG y hy).sub (Real.hasDerivAt_exp y)).deriv
    refine ⟨G x₀ - Real.exp x₀, ?_⟩
    intro x hx
    have hc := hOpen.is_const_of_deriv_eq_zero hConn hdiff hzero hx hx₀
    change G x - Real.exp x = G x₀ - Real.exp x₀ at hc
    linarith
  · refine ⟨0, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

private theorem expanded_base_eq_primitive (x : ℝ) (hx : x ≠ -1) :
    -x * Real.exp x / (x + 1) + Real.exp x = primitive x := by
  have hden : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  unfold primitive
  field_simp [hden] <;> ring

theorem gap1 (U : Set ℝ) (hU : Regular U) :
    Family U f = Step1 U := by
  ext F
  change (F ∈ Family U f ↔ F ∈ Step1 U)
  constructor
  · intro hF
    change ∀ x ∈ U, HasDerivAt F (f x) x at hF
    change ∃ G ∈ Family U (fun x => x * Real.exp x * deriv (fun y => 1 / (y + 1)) x),
      ∃ C, ∀ x ∈ U, F x = -G x + C
    refine ⟨fun y => -F y, ?_, 0, ?_⟩
    · change ∀ x ∈ U, HasDerivAt (fun y => -F y)
        (x * Real.exp x * deriv (fun y => 1 / (y + 1)) x) x
      intro x hx
      convert (hF x hx).neg using 1
      exact reciprocal_integrand_eq_neg_f x (hU.2.2 x hx)
    · intro x hx
      ring
  · intro hS
    change ∃ G ∈ Family U (fun x => x * Real.exp x * deriv (fun y => 1 / (y + 1)) x),
      ∃ C, ∀ x ∈ U, F x = -G x + C at hS
    rcases hS with ⟨G, hG, C, hEq⟩
    change ∀ x ∈ U, HasDerivAt F (f x) x
    intro x hx
    have hH : HasDerivAt (fun y => -G y + C) (f x) x := by
      have hd := (hG x hx).neg.add_const C
      convert hd using 1
      change f x = -(x * Real.exp x * deriv (fun y => 1 / (y + 1)) x)
      linarith [reciprocal_integrand_eq_neg_f x (hU.2.2 x hx)]
    exact hasDerivAt_of_eqOn_open hU.1 hx hEq hH
theorem gap2 (U : Set ℝ) (hU : Regular U) :
    Family U f = Step2 U := by
  ext F
  change (F ∈ Family U f ↔ F ∈ Step2 U)
  constructor
  · intro hF
    change ∀ x ∈ U, HasDerivAt F (f x) x at hF
    change ∃ G ∈ Family U Real.exp, ∃ C, ∀ x ∈ U,
      F x = -x * Real.exp x / (x + 1) + G x + C
    refine ⟨fun y => F y + y * Real.exp y / (y + 1), ?_, 0, ?_⟩
    · change ∀ x ∈ U, HasDerivAt
        (fun y => F y + y * Real.exp y / (y + 1)) (Real.exp x) x
      intro x hx
      have hd := (hF x hx).add
        (quotient_term_hasDerivAt x (hU.2.2 x hx))
      convert hd using 1
      ring
    · intro x hx
      ring
  · intro hS
    change ∃ G ∈ Family U Real.exp, ∃ C, ∀ x ∈ U,
      F x = -x * Real.exp x / (x + 1) + G x + C at hS
    rcases hS with ⟨G, hG, C, hEq⟩
    change ∀ x ∈ U, HasDerivAt F (f x) x
    intro x hx
    have hd := ((quotient_term_hasDerivAt x (hU.2.2 x hx)).neg.add
      (hG x hx)).add_const C
    have hd' : HasDerivAt
        (fun y => ((-(fun z : ℝ => z * Real.exp z / (z + 1))) + G) y + C)
        (f x) x := by
      convert hd using 1
      ring
    apply hasDerivAt_of_eqOn_open hU.1 hx _ hd'
    intro y hy
    rw [hEq y hy]
    dsimp
    ring
theorem gap3 (U : Set ℝ) (hU : Regular U) :
    Step2 U = Expanded U := by
  ext F
  change (F ∈ Step2 U ↔ F ∈ Expanded U)
  constructor
  · intro hS
    change ∃ G ∈ Family U Real.exp, ∃ C, ∀ x ∈ U,
      F x = -x * Real.exp x / (x + 1) + G x + C at hS
    rcases hS with ⟨G, hG, C, hEq⟩
    obtain ⟨d, hd⟩ := family_exp_is_translate U hU.1 hU.2.1 hG
    change ∃ C, ∀ x ∈ U,
      F x = -x * Real.exp x / (x + 1) + Real.exp x + C
    refine ⟨d + C, ?_⟩
    intro x hx
    rw [hEq x hx, hd x hx]
    ring
  · intro hE
    change ∃ C, ∀ x ∈ U,
      F x = -x * Real.exp x / (x + 1) + Real.exp x + C at hE
    rcases hE with ⟨C, hEq⟩
    change ∃ G ∈ Family U Real.exp, ∃ C, ∀ x ∈ U,
      F x = -x * Real.exp x / (x + 1) + G x + C
    refine ⟨Real.exp, ?_, C, hEq⟩
    intro x hx
    exact Real.hasDerivAt_exp x
theorem gap4 (U : Set ℝ) (hU : Regular U) :
    Expanded U = Translates U primitive := by
  ext F
  change (F ∈ Expanded U ↔ F ∈ Translates U primitive)
  constructor
  · intro hE
    change ∃ C, ∀ x ∈ U,
      F x = -x * Real.exp x / (x + 1) + Real.exp x + C at hE
    rcases hE with ⟨C, hEq⟩
    change ∃ C, ∀ x ∈ U, F x = primitive x + C
    refine ⟨C, ?_⟩
    intro x hx
    calc
      F x = (-x * Real.exp x / (x + 1) + Real.exp x) + C := hEq x hx
      _ = primitive x + C := by
        rw [expanded_base_eq_primitive x (hU.2.2 x hx)]
  · intro hT
    change ∃ C, ∀ x ∈ U, F x = primitive x + C at hT
    rcases hT with ⟨C, hEq⟩
    change ∃ C, ∀ x ∈ U,
      F x = -x * Real.exp x / (x + 1) + Real.exp x + C
    refine ⟨C, ?_⟩
    intro x hx
    calc
      F x = primitive x + C := hEq x hx
      _ = (-x * Real.exp x / (x + 1) + Real.exp x) + C := by
        rw [expanded_base_eq_primitive x (hU.2.2 x hx)]
theorem gap5 (U : Set ℝ) (hU : Regular U) :
    Family U f = Translates U primitive := by
  calc
    Family U f = Step2 U := gap2 U hU
    _ = Expanded U := gap3 U hU
    _ = Translates U primitive := gap4 U hU

end
end ProofGap.Exercise2096
