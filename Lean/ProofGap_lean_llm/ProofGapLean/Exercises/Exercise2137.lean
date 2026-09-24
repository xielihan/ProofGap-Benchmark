import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2137
noncomputable section

def AdmissibleBranch (U : Set ℝ) : Prop :=
  U = Set.Ioo (-1) 0 ∨ U = Set.Ioo 0 1
def integrand (x : ℝ) :=
  (1 + Real.sqrt (1 - x ^ 2)) / (1 - Real.sqrt (1 - x ^ 2))
def rationalized (x : ℝ) :=
  ((1 + Real.sqrt (1 - x ^ 2)) * (1 + Real.sqrt (1 - x ^ 2))) /
    ((1 - Real.sqrt (1 - x ^ 2)) * (1 + Real.sqrt (1 - x ^ 2)))
def expanded (x : ℝ) :=
  (2 - x ^ 2 + 2 * Real.sqrt (1 - x ^ 2)) / x ^ 2
def reciprocalDifferential (x : ℝ) :=
  Real.sqrt (1 - x ^ 2) * deriv (fun y : ℝ => 1 / y) x
def arcsinIntegrand (x : ℝ) := 1 / Real.sqrt (1 - x ^ 2)
def primitive (x : ℝ) :=
  -(2 + x ^ 2) / x - 2 / x * Real.sqrt (1 - x ^ 2) - 2 * Real.arcsin x

def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def Stage3 (U : Set ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family U reciprocalDifferential, ∀ x ∈ U,
    F x = -2 / x - x - 2 * A x}
def Stage5 (U : Set ℝ) :=
  {F : ℝ → ℝ | ∃ A ∈ Family U arcsinIntegrand, ∀ x ∈ U,
    F x = -2 / x - x - 2 / x * Real.sqrt (1 - x ^ 2) - 2 * A x}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ U, F x = p x + C}

private lemma admissible_mem_facts {U : Set ℝ} (hU : AdmissibleBranch U)
    {x : ℝ} (hx : x ∈ U) :
    x ≠ 0 ∧ 0 < 1 - x ^ 2 ∧ x ∈ Set.Ioo (-1 : ℝ) 1 := by
  rcases hU with rfl | rfl
  · have hxm : -1 < x := hx.1
    have hxz : x < 0 := hx.2
    have hp : 0 < (1 - x) * (1 + x) :=
      mul_pos (by linarith) (by linarith)
    refine ⟨by linarith, ?_, ⟨by linarith, by linarith⟩⟩
    nlinarith
  · have hxz : 0 < x := hx.1
    have hxo : x < 1 := hx.2
    have hp : 0 < (1 - x) * (1 + x) :=
      mul_pos (by linarith) (by linarith)
    refine ⟨by linarith, ?_, ⟨by linarith, by linarith⟩⟩
    nlinarith

private lemma integrand_eq_rationalized {U : Set ℝ}
    (hU : AdmissibleBranch U) {x : ℝ} (hx : x ∈ U) :
    integrand x = rationalized x := by
  obtain ⟨hx0, hpos, _⟩ := admissible_mem_facts hU hx
  have hspos : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hpos
  have hs_sq : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hpos)
  have hm : 1 - Real.sqrt (1 - x ^ 2) ≠ 0 := by
    intro hm
    have hs : Real.sqrt (1 - x ^ 2) = 1 := by linarith
    rw [hs] at hs_sq
    have hx_sq : x ^ 2 = 0 := by
      nlinarith [hs_sq]
    exact (pow_ne_zero 2 hx0) hx_sq
  have hp : 1 + Real.sqrt (1 - x ^ 2) ≠ 0 := by
    positivity
  unfold integrand rationalized
  field_simp [hm, hp]

private lemma rationalized_eq_expanded {U : Set ℝ}
    (hU : AdmissibleBranch U) {x : ℝ} (hx : x ∈ U) :
    rationalized x = expanded x := by
  obtain ⟨_, hpos, _⟩ := admissible_mem_facts hU hx
  have hs_sq : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hpos)
  unfold rationalized expanded
  congr 1 <;> nlinarith

private lemma integrand_eq_expanded {U : Set ℝ}
    (hU : AdmissibleBranch U) {x : ℝ} (hx : x ∈ U) :
    integrand x = expanded x := by
  exact (integrand_eq_rationalized hU hx).trans
    (rationalized_eq_expanded hU hx)

private lemma family_eq_of_eqOn {U : Set ℝ} {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ U, f x = g x) : Family U f = Family U g := by
  apply Set.ext
  intro F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    simpa only [hfg x hx] using hF x hx
  · intro hF x hx
    simpa only [hfg x hx] using hF x hx

private lemma deriv_reciprocal {x : ℝ} (hx : x ≠ 0) :
    deriv (fun y : ℝ => 1 / y) x = -1 / x ^ 2 := by
  have h := (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx
  convert h.deriv using 1 <;> simp <;> field_simp [hx] <;> ring

private lemma expanded_stage3_coefficient {x : ℝ} (hx : x ≠ 0) :
    expanded x = 2 / x ^ 2 - 1 - 2 * reciprocalDifferential x := by
  rw [reciprocalDifferential, deriv_reciprocal hx]
  unfold expanded
  field_simp [hx]
  ring

private lemma hasDerivAt_stage3_form {A : ℝ → ℝ} {x : ℝ}
    (hx : x ≠ 0)
    (hA : HasDerivAt A (reciprocalDifferential x) x) :
    HasDerivAt (fun y : ℝ => -2 / y - y - 2 * A y) (expanded x) x := by
  have hq : HasDerivAt (fun y : ℝ => -2 / y) (2 / x ^ 2) x := by
    have h := (hasDerivAt_const x (-2 : ℝ)).div (hasDerivAt_id x) hx
    convert h using 1 <;> simp <;> field_simp [hx] <;> ring
  have h := (hq.sub (hasDerivAt_id x)).sub
    ((hasDerivAt_const x (2 : ℝ)).mul hA)
  rw [expanded_stage3_coefficient hx]
  convert h using 1 <;> ring

private lemma hasDerivAt_congr_Ioo {a b x d : ℝ} {f g : ℝ → ℝ}
    (hx : x ∈ Set.Ioo a b)
    (hfg : ∀ y ∈ Set.Ioo a b, f y = g y)
    (hg : HasDerivAt g d x) : HasDerivAt f d x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact hfg y hy

private lemma family_expanded_eq_stage3 (U : Set ℝ)
    (hU : AdmissibleBranch U) : Family U expanded = Stage3 U := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ U, HasDerivAt F (expanded x) x at hF
    let A : ℝ → ℝ := fun y => (1 / 2 : ℝ) * (-2 / y - y - F y)
    change ∃ A ∈ Family U reciprocalDifferential, ∀ x ∈ U,
      F x = -2 / x - x - 2 * A x
    refine ⟨A, ?_, ?_⟩
    · change ∀ x ∈ U, HasDerivAt A (reciprocalDifferential x) x
      intro x hxU
      obtain ⟨hx, _, _⟩ := admissible_mem_facts hU hxU
      have hq : HasDerivAt (fun y : ℝ => -2 / y) (2 / x ^ 2) x := by
        have h := (hasDerivAt_const x (-2 : ℝ)).div (hasDerivAt_id x) hx
        convert h using 1 <;> simp <;> field_simp [hx] <;> ring
      have hd := (hq.sub (hasDerivAt_id x)).sub (hF x hxU)
      have hmul := (hasDerivAt_const x (1 / 2 : ℝ)).mul hd
      dsimp only [A]
      rw [expanded_stage3_coefficient hx] at hmul
      convert hmul using 1 <;> ring
    · intro x hx
      dsimp only [A]
      ring
  · intro hF
    change ∃ A ∈ Family U reciprocalDifferential, ∀ x ∈ U,
      F x = -2 / x - x - 2 * A x at hF
    rcases hF with ⟨A, hA, hEq⟩
    change ∀ x ∈ U, HasDerivAt F (expanded x) x
    intro x hxU
    obtain ⟨hx, _, _⟩ := admissible_mem_facts hU hxU
    rcases hU with rfl | rfl
    · exact hasDerivAt_congr_Ioo hxU hEq
        (hasDerivAt_stage3_form hx (hA x hxU))
    · exact hasDerivAt_congr_Ioo hxU hEq
        (hasDerivAt_stage3_form hx (hA x hxU))

private lemma hasDerivAt_arcsin_on_admissible {U : Set ℝ}
    (hU : AdmissibleBranch U) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt Real.arcsin (arcsinIntegrand x) x := by
  obtain ⟨_, _, hxi⟩ := admissible_mem_facts hU hx
  unfold arcsinIntegrand
  exact Real.hasDerivAt_arcsin (ne_of_gt hxi.1) (ne_of_lt hxi.2)

private lemma hasDerivAt_primitive {U : Set ℝ}
    (hU : AdmissibleBranch U) {x : ℝ} (hxU : x ∈ U) :
    HasDerivAt primitive (integrand x) x := by
  obtain ⟨hx, hpos, hxi⟩ := admissible_mem_facts hU hxU
  have hspos : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hpos
  have hs_sq : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hpos)
  have hinner : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      simp <;> ring
  have hsqrt : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      (-x / Real.sqrt (1 - x ^ 2)) x := by
    have h := (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp x hinner
    convert h using 1 <;> field_simp [ne_of_gt hspos] <;> ring
  have harc : HasDerivAt Real.arcsin
      (1 / Real.sqrt (1 - x ^ 2)) x :=
    Real.hasDerivAt_arcsin (ne_of_gt hxi.1) (ne_of_lt hxi.2)
  have hfirst : HasDerivAt (fun y : ℝ => -(2 + y ^ 2) / y)
      (2 / x ^ 2 - 1) x := by
    have hnum := ((hasDerivAt_const x (2 : ℝ)).add
      ((hasDerivAt_id x).pow 2)).neg
    have h := hnum.div (hasDerivAt_id x) hx
    convert h using 1 <;> simp <;> field_simp [hx] <;> ring
  have hquot : HasDerivAt (fun y : ℝ => 2 / y) (-2 / x ^ 2) x := by
    have h := (hasDerivAt_const x (2 : ℝ)).div (hasDerivAt_id x) hx
    convert h using 1 <;> simp <;> field_simp [hx] <;> ring
  have hall := (hfirst.sub (hquot.mul hsqrt)).sub
    ((hasDerivAt_const x (2 : ℝ)).mul harc)
  change HasDerivAt
    (fun y : ℝ => -(2 + y ^ 2) / y - 2 / y * Real.sqrt (1 - y ^ 2) -
      2 * Real.arcsin y) (integrand x) x
  rw [integrand_eq_expanded hU hxU]
  unfold expanded
  convert hall using 1 <;> field_simp [hx, ne_of_gt hspos] <;> ring

private lemma family_Ioo_eq_translates {a b : ℝ} (hab : a < b)
    {f p : ℝ → ℝ}
    (hp : ∀ x ∈ Set.Ioo a b, HasDerivAt p (f x) x) :
    Family (Set.Ioo a b) f = Translates (Set.Ioo a b) p := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ Set.Ioo a b, HasDerivAt F (f x) x at hF
    let D : ℝ → ℝ := fun y => F y - p y
    have hdiff : DifferentiableOn ℝ D (Set.Ioo a b) := by
      intro x hx
      exact ((hF x hx).sub (hp x hx)).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ Set.Ioo a b, deriv D x = 0 := by
      intro x hx
      change deriv (F - p) x = 0
      simpa using ((hF x hx).sub (hp x hx)).deriv
    let x₀ : ℝ := (a + b) / 2
    have hx₀ : x₀ ∈ Set.Ioo a b := by
      dsimp only [x₀]
      constructor <;> linarith
    change ∃ C : ℝ, ∀ x ∈ Set.Ioo a b, F x = p x + C
    refine ⟨D x₀, ?_⟩
    intro x hx
    have heq : D x = D x₀ :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero hx hx₀
    dsimp only [D] at heq ⊢
    linarith
  · intro hF
    change ∃ C : ℝ, ∀ x ∈ Set.Ioo a b, F x = p x + C at hF
    rcases hF with ⟨C, hEq⟩
    change ∀ x ∈ Set.Ioo a b, HasDerivAt F (f x) x
    intro x hx
    exact hasDerivAt_congr_Ioo hx hEq ((hp x hx).add_const C)

private lemma family_eq_translates_of_primitive {U : Set ℝ}
    (hU : AdmissibleBranch U) {f p : ℝ → ℝ}
    (hp : ∀ x ∈ U, HasDerivAt p (f x) x) :
    Family U f = Translates U p := by
  rcases hU with rfl | rfl
  · exact family_Ioo_eq_translates (by norm_num) hp
  · exact family_Ioo_eq_translates (by norm_num) hp

private lemma family_integrand_eq_translates {U : Set ℝ}
    (hU : AdmissibleBranch U) :
    Family U integrand = Translates U primitive := by
  apply family_eq_translates_of_primitive hU
  intro x hx
  exact hasDerivAt_primitive hU hx

private lemma stage5_eq_translates {U : Set ℝ}
    (hU : AdmissibleBranch U) : Stage5 U = Translates U primitive := by
  have hArc : Family U arcsinIntegrand = Translates U Real.arcsin := by
    apply family_eq_translates_of_primitive hU
    intro x hx
    exact hasDerivAt_arcsin_on_admissible hU hx
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∃ A ∈ Family U arcsinIntegrand, ∀ x ∈ U,
      F x = -2 / x - x - 2 / x * Real.sqrt (1 - x ^ 2) - 2 * A x at hF
    rcases hF with ⟨A, hA, hEq⟩
    have hAT : A ∈ Translates U Real.arcsin := by
      rw [← hArc]
      exact hA
    change ∃ C : ℝ, ∀ x ∈ U, A x = Real.arcsin x + C at hAT
    rcases hAT with ⟨C, hAC⟩
    change ∃ C : ℝ, ∀ x ∈ U, F x = primitive x + C
    refine ⟨-2 * C, ?_⟩
    intro x hx
    obtain ⟨hx0, _, _⟩ := admissible_mem_facts hU hx
    rw [hEq x hx, hAC x hx]
    unfold primitive
    field_simp [hx0] <;> ring
  · intro hF
    change ∃ C : ℝ, ∀ x ∈ U, F x = primitive x + C at hF
    rcases hF with ⟨C, hEq⟩
    let A : ℝ → ℝ := fun x => Real.arcsin x - C / 2
    change ∃ A ∈ Family U arcsinIntegrand, ∀ x ∈ U,
      F x = -2 / x - x - 2 / x * Real.sqrt (1 - x ^ 2) - 2 * A x
    refine ⟨A, ?_, ?_⟩
    · change ∀ x ∈ U, HasDerivAt A (arcsinIntegrand x) x
      intro x hx
      dsimp only [A]
      exact (hasDerivAt_arcsin_on_admissible hU hx).sub_const (C / 2)
    · intro x hx
      obtain ⟨hx0, _, _⟩ := admissible_mem_facts hU hx
      rw [hEq x hx]
      dsimp only [A]
      unfold primitive
      field_simp [hx0] <;> ring

theorem gap1 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Family U rationalized := by
  apply family_eq_of_eqOn
  intro x hx
  exact integrand_eq_rationalized hU hx
theorem gap2 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Family U expanded := by
  apply family_eq_of_eqOn
  intro x hx
  exact integrand_eq_expanded hU hx
theorem gap3 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U expanded = Stage3 U := by
  exact family_expanded_eq_stage3 (U := U) hU
theorem gap4 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Stage3 U := by
  calc
    Family U integrand = Family U expanded := gap2 U hU
    _ = Stage3 U := gap3 U hU
theorem gap5 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Stage5 U := by
  calc
    Family U integrand = Translates U primitive := family_integrand_eq_translates hU
    _ = Stage5 U := (stage5_eq_translates hU).symm
theorem gap6 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Stage5 U = Translates U primitive := by
  exact stage5_eq_translates hU
theorem gap7 (U : Set ℝ) (hU : AdmissibleBranch U) :
    Family U integrand = Translates U primitive := by
  exact family_integrand_eq_translates hU

end
end ProofGap.Exercise2137
