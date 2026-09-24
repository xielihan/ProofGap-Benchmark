import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1680

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / (Real.sqrt x * (1 + x))
def primitive (x : ℝ) : ℝ := 2 * Real.arctan (Real.sqrt x)
def domain : Set ℝ := Set.Ioi 0

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    integrand x =
      2 * deriv Real.sqrt x / (1 + (Real.sqrt x) ^ 2) := by
  have hxpos : 0 < x := by
    simpa [domain] using hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hsqrt : Real.sqrt x ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hxpos)
  have hden : 1 + x ≠ 0 :=
    ne_of_gt (add_pos zero_lt_one hxpos)
  unfold integrand
  rw [(Real.hasDerivAt_sqrt hx0).deriv,
    Real.sq_sqrt (le_of_lt hxpos)]
  field_simp [hsqrt, hden]

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have hxpos : 0 < x := by
    simpa [domain] using hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hsqrt : HasDerivAt Real.sqrt (deriv Real.sqrt x) x :=
    (Real.hasDerivAt_sqrt hx0).congr_deriv
      (Real.hasDerivAt_sqrt hx0).deriv.symm
  have harctan :
      HasDerivAt Real.arctan (deriv Real.arctan (Real.sqrt x))
        (Real.sqrt x) :=
    (Real.hasDerivAt_arctan (Real.sqrt x)).congr_deriv
      (Real.hasDerivAt_arctan (Real.sqrt x)).deriv.symm
  have hchain := (harctan.comp x hsqrt).const_mul 2
  have heq :
      2 * (deriv Real.arctan (Real.sqrt x) * deriv Real.sqrt x) =
        integrand x := by
    rw [(Real.hasDerivAt_arctan (Real.sqrt x)).deriv, gap1 x hx]
    ring
  simpa only [primitive, Function.comp_apply] using hchain.congr_deriv heq

theorem gap3 :
    Family integrand domain = Translates primitive domain := by
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand domain at hF
    change ∃ C, ∀ x ∈ domain, F x = primitive x + C
    have hzero :
        ∀ x ∈ domain,
          HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (gap2 x hx)
    have hgdiff :
        DifferentiableOn ℝ (fun y => F y - primitive y) domain := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hopen : IsOpen domain := by
      rw [domain]
      exact isOpen_Ioi
    have hconn : IsPreconnected domain := by
      simpa [domain] using (convex_Ioi (0 : ℝ)).isPreconnected
    have hone : (1 : ℝ) ∈ domain := by
      simp [domain]
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have heq : F x - primitive x = F 1 - primitive 1 :=
      hopen.is_const_of_deriv_eq_zero hconn hgdiff
        (fun y hy => (hzero y hy).deriv) hx hone
    calc
      F x = primitive x + (F x - primitive x) := by ring
      _ = primitive x + (F 1 - primitive 1) := by rw [heq]
  · intro hF
    change ∃ C, ∀ x ∈ domain, F x = primitive x + C at hF
    rcases hF with ⟨C, hC⟩
    change IsAntiderivativeOn F integrand domain
    intro x hx
    have hopen : IsOpen domain := by
      rw [domain]
      exact isOpen_Ioi
    have hnhds : ∀ᶠ y in nhds x, y ∈ domain :=
      hopen.mem_nhds hx
    have hevent : F =ᶠ[nhds x] fun y => primitive y + C :=
      hnhds.mono (fun y hy => hC y hy)
    exact (hevent.hasDerivAt_iff).2 ((gap2 x hx).add_const C)

end

end ProofGap.Exercise1680
