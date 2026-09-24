import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1659

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / (Real.sqrt (5 * x - 2)) ^ 5
def primitive (x : ℝ) : ℝ := -2 / (15 * (Real.sqrt (5 * x - 2)) ^ 3)
def domain : Set ℝ := Set.Ioi (2 / 5 : ℝ)

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt
      (fun y => (1 / 5 : ℝ) * (-2 / 3) /
        (Real.sqrt (5 * y - 2)) ^ 3) (integrand x) x := by
  have hpos : 0 < 5 * x - 2 := by
    change (2 / 5 : ℝ) < x at hx
    linarith
  have hsne : Real.sqrt (5 * x - 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  have hinner : HasDerivAt (fun y : ℝ => 5 * y - 2) 5 x := by
    convert ((hasDerivAt_id x).const_mul 5).sub_const 2 using 1 <;> ring
  have hsqrt :=
    (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp x hinner
  have hpow : HasDerivAt (fun y => (Real.sqrt (5 * y - 2)) ^ 3)
      (3 * (Real.sqrt (5 * x - 2)) ^ 2 *
        (1 / (2 * Real.sqrt (5 * x - 2)) * 5)) x := by
    simpa only [Function.comp_apply, Nat.cast_ofNat, Nat.reduceSub] using hsqrt.pow 3
  have hquot :=
    (hasDerivAt_const x ((1 / 5 : ℝ) * (-2 / 3))).div hpow
      (pow_ne_zero 3 hsne)
  convert hquot using 1
  unfold integrand
  field_simp [hsne]
  ring

theorem gap2 (x : ℝ) :
    (1 / 5 : ℝ) * (-2 / 3) / (Real.sqrt (5 * x - 2)) ^ 3 =
      primitive x := by
  unfold primitive
  ring

theorem gap3 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  have hprimitive : IsAntiderivativeOn primitive integrand s := by
    intro x hx
    simpa only [gap2] using gap1 x (hdom hx)
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

end ProofGap.Exercise1659
