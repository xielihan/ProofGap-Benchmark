import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1669

noncomputable section

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def integrand (x : ℝ) : ℝ := 1 / (1 - Real.cos x)
def primitive (x : ℝ) : ℝ := -cot (x / 2)
def domain : Set ℝ := {x | Real.sin (x / 2) ≠ 0}

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

theorem gap1 (x : ℝ) :
    1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
  have hcos : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (x / 2) using 1 <;> ring
  rw [hcos]
  nlinarith [Real.sin_sq_add_cos_sq (x / 2)]

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have hsin : Real.sin (x / 2) ≠ 0 := hx
  have hhalf : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id x).mul_const (1 / 2)
  have hsinDeriv : HasDerivAt (fun y : ℝ => Real.sin (y / 2))
      (Real.cos (x / 2) * (1 / 2)) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sin (x / 2)).comp x hhalf
  have hcosDeriv : HasDerivAt (fun y : ℝ => Real.cos (y / 2))
      (-Real.sin (x / 2) * (1 / 2)) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_cos (x / 2)).comp x hhalf
  have hquot : HasDerivAt (fun y : ℝ => Real.cos (y / 2) / Real.sin (y / 2))
      (((-Real.sin (x / 2) * (1 / 2)) * Real.sin (x / 2) -
        Real.cos (x / 2) * (Real.cos (x / 2) * (1 / 2))) /
        Real.sin (x / 2) ^ 2) x :=
    hcosDeriv.div hsinDeriv hsin
  have hprim : HasDerivAt primitive
      (-(((-Real.sin (x / 2) * (1 / 2)) * Real.sin (x / 2) -
        Real.cos (x / 2) * (Real.cos (x / 2) * (1 / 2))) /
        Real.sin (x / 2) ^ 2)) x := by
    simpa [primitive, cot] using hquot.neg
  convert hprim using 1
  change 1 / (1 - Real.cos x) = _
  rw [gap1 x]
  field_simp [hsin]
  nlinarith [Real.sin_sq_add_cos_sq (x / 2)]

theorem gap3 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  ext F
  constructor
  · intro hF
    have hP : IsAntiderivativeOn primitive integrand s := by
      intro x hx
      exact gap2 x (hdom hx)
    have hzero : ∀ x ∈ s, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (hP x hx)
    rcases isEmpty_or_nonempty s with hs_empty | hs_nonempty
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hs_empty.false ⟨x, hx⟩).elim
    · rcases hs_nonempty with ⟨⟨x₀, hx₀⟩⟩
      refine ⟨F x₀ - primitive x₀, ?_⟩
      intro x hx
      have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y) s := by
        intro y hy
        exact (hzero y hy).differentiableAt.differentiableWithinAt
      have hderiv : ∀ y ∈ s, deriv (fun z => F z - primitive z) y = 0 := by
        intro y hy
        exact (hzero y hy).deriv
      have hconst : F x - primitive x = F x₀ - primitive x₀ :=
        hopen.is_const_of_deriv_eq_zero hs hdiff hderiv hx hx₀
      linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have hP := gap2 x (hdom hx)
    have hlocal : F =ᶠ[nhds x] fun y => C + primitive y := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      simpa [add_comm] using hC y hy
    exact (hP.const_add C).congr_of_eventuallyEq hlocal

end

end ProofGap.Exercise1669
