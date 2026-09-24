import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1751

noncomputable section

def domain : Set ℝ := Set.Ioo 0 Real.pi
def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def csc (x : ℝ) : ℝ := 1 / Real.sin x
def original (x : ℝ) : ℝ := cot x ^ 2
def reduced (x : ℝ) : ℝ := csc x ^ 2 - 1
def primitive (x : ℝ) : ℝ := -cot x - x
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem original_eq_reduced (x : ℝ) (hx : x ∈ domain) :
    original x = reduced x := by
  have hsin_pos : 0 < Real.sin x := by
    exact Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hsin : Real.sin x ≠ 0 := ne_of_gt hsin_pos
  unfold original reduced cot csc
  field_simp [hsin]
  nlinarith [Real.sin_sq_add_cos_sq x]

private theorem hasDerivAt_primitive (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (reduced x) x := by
  have hsin_pos : 0 < Real.sin x := by
    exact Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hsin : Real.sin x ≠ 0 := ne_of_gt hsin_pos
  have hcoef :
      ((-Real.sin x) * Real.sin x - Real.cos x * Real.cos x) /
          Real.sin x ^ 2 = -1 / Real.sin x ^ 2 := by
    field_simp [hsin]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hquot := (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hsin
  rw [hcoef] at hquot
  have hcot : HasDerivAt cot (-1 / Real.sin x ^ 2) x := by
    simpa only [cot] using hquot
  have hp := hcot.neg.sub (hasDerivAt_id x)
  have hvalue : -(-1 / Real.sin x ^ 2) - 1 = reduced x := by
    unfold reduced csc
    field_simp [hsin]
  rw [hvalue] at hp
  simpa only [primitive, id_eq] using hp

theorem gap1 : AntiderivativesOn original = AntiderivativesOn reduced := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = original x := hderiv x hx
      _ = reduced x := original_eq_reduced x hx
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = reduced x := hderiv x hx
      _ = original x := (original_eq_reduced x hx).symm

theorem gap2 : AntiderivativesOn reduced = PrimitiveFamily primitive := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    have hopen : IsOpen domain := by
      simpa [domain] using (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) Real.pi))
    have hp : DifferentiableOn ℝ primitive domain := by
      intro x hx
      exact (hasDerivAt_primitive x hx).differentiableAt.differentiableWithinAt
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y) domain :=
      hF.sub hp
    have hzero :
        ∀ x ∈ domain, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      have hFx : DifferentiableAt ℝ F x :=
        (hF x hx).differentiableAt (hopen.mem_nhds hx)
      have hFhas : HasDerivAt F (reduced x) x := by
        simpa only [hderiv x hx] using hFx.hasDerivAt
      have hsub : HasDerivAt (fun y => F y - primitive y) 0 x := by
        simpa using hFhas.sub (hasDerivAt_primitive x hx)
      exact hsub.deriv
    have hdiffI :
        DifferentiableOn ℝ (fun y => F y - primitive y)
          (Set.Ioo (0 : ℝ) Real.pi) := by
      simpa only [domain] using hdiff
    have hzeroI :
        ∀ x ∈ Set.Ioo (0 : ℝ) Real.pi,
          deriv (fun y => F y - primitive y) x = 0 := by
      simpa only [domain] using hzero
    have href : Real.pi / 2 ∈ Set.Ioo (0 : ℝ) Real.pi := by
      constructor <;> nlinarith [Real.pi_pos]
    refine ⟨F (Real.pi / 2) - primitive (Real.pi / 2), ?_⟩
    intro x hx
    have hxI : x ∈ Set.Ioo (0 : ℝ) Real.pi := by
      simpa only [domain] using hx
    have heq :
        (fun y => F y - primitive y) x =
          (fun y => F y - primitive y) (Real.pi / 2) := by
      exact
        isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
          hdiffI hzeroI hxI href
    linarith
  · rintro ⟨C, hC⟩
    have hopen : IsOpen domain := by
      simpa [domain] using (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) Real.pi))
    have hhas : ∀ x ∈ domain, HasDerivAt F (reduced x) x := by
      intro x hx
      have hbase : HasDerivAt (fun y => primitive y + C) (reduced x) x :=
        (hasDerivAt_primitive x hx).add_const C
      have hevent : F =ᶠ[nhds x] (fun y => primitive y + C) := by
        filter_upwards [hopen.mem_nhds hx] with y hy
        exact hC y hy
      exact hbase.congr_of_eventuallyEq hevent
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hhas x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hhas x hx).deriv

theorem gap3 : AntiderivativesOn original = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1751
