import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1685

noncomputable section

def inner (x : ℝ) : ℝ := x ^ 2 - 1
def integrand (x : ℝ) : ℝ := x / (Real.sqrt (inner x)) ^ 3
def primitive (x : ℝ) : ℝ := -1 / Real.sqrt (inner x)
def domain : Set ℝ := {x | 1 < |x|}

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem inner_hasDerivAt (x : ℝ) :
    HasDerivAt inner (2 * x) x := by
  unfold inner
  convert ((hasDerivAt_id x).pow 2).sub_const 1 using 1 <;>
    simp only [id_eq] <;>
    ring

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    integrand x =
      (1 / 2 : ℝ) * deriv inner x / (Real.sqrt (inner x)) ^ 3 := by
  rw [(inner_hasDerivAt x).deriv]
  unfold integrand
  ring

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have hxabs : 1 < |x| := hx
  have hxsq : 1 < x ^ 2 := by
    nlinarith [sq_abs x, sq_nonneg |x|]
  have hpos : 0 < inner x := by
    unfold inner
    linarith
  have hsne : Real.sqrt (inner x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  have hs :=
    (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp x (inner_hasDerivAt x)
  have hquot := (hasDerivAt_const x (-1 : ℝ)).div hs hsne
  unfold primitive
  convert hquot using 1
  unfold integrand
  simp only [Function.comp_apply]
  field_simp [hsne]
  ring

theorem gap3 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  have hprimitive : IsAntiderivativeOn primitive integrand s := by
    intro x hx
    exact gap2 x (hdom hx)
  apply Set.ext
  intro F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand s at hF
    change ∃ C, ∀ x ∈ s, F x = primitive x + C
    have hzero : ∀ x ∈ s,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (hprimitive x hx)
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y) s := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ s, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      exact (hzero x hx).deriv
    by_cases hempty : s.Nonempty
    · obtain ⟨x₀, hx₀⟩ := hempty
      refine ⟨F x₀ - primitive x₀, ?_⟩
      intro x hx
      have heq : F x - primitive x = F x₀ - primitive x₀ :=
        IsOpen.is_const_of_deriv_eq_zero hopen hs hdiff hderiv hx hx₀
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact False.elim (hempty ⟨x, hx⟩)
  · rintro ⟨C, hC⟩
    change IsAntiderivativeOn F integrand s
    intro x hx
    apply ((hprimitive x hx).add_const C).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hC y hy

end

end ProofGap.Exercise1685
