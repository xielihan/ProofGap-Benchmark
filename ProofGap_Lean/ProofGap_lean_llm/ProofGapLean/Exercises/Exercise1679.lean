import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1679

noncomputable section

def inner (x : ℝ) : ℝ := x ^ 4
def integrand (x : ℝ) : ℝ := x ^ 3 / (x ^ 8 - 2)
def primitive (x : ℝ) : ℝ :=
  1 / (8 * Real.sqrt 2) *
    Real.log |(x ^ 4 - Real.sqrt 2) / (x ^ 4 + Real.sqrt 2)|
def domain : Set ℝ := {x | x ^ 8 ≠ 2}

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    integrand x =
      (1 / 4 : ℝ) * deriv inner x / (inner x ^ 2 - (Real.sqrt 2) ^ 2) := by
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hinner : HasDerivAt inner (4 * x ^ 3) x := by
    simpa [inner] using (hasDerivAt_id x).pow 4
  rw [hinner.deriv, hsqrt_sq]
  dsimp [integrand, inner]
  ring

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have hx8 : x ^ 8 ≠ (2 : ℝ) := by
    simpa [domain] using hx
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt_pos
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hx4_nonneg : 0 ≤ x ^ 4 := by positivity
  have hnum : x ^ 4 - Real.sqrt 2 ≠ 0 := by
    intro hzero
    apply hx8
    have heq : x ^ 4 = Real.sqrt 2 := sub_eq_zero.mp hzero
    calc
      x ^ 8 = (x ^ 4) ^ 2 := by ring
      _ = (Real.sqrt 2) ^ 2 := by rw [heq]
      _ = 2 := hsqrt_sq
  have hden : x ^ 4 + Real.sqrt 2 ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos hx4_nonneg hsqrt_pos)
  have hquot : (x ^ 4 - Real.sqrt 2) / (x ^ 4 + Real.sqrt 2) ≠ 0 :=
    div_ne_zero hnum hden
  have hpow : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
    simpa using (hasDerivAt_id x).pow 4
  have hnumDeriv :
      HasDerivAt (fun y : ℝ => y ^ 4 - Real.sqrt 2) (4 * x ^ 3) x :=
    hpow.sub_const (Real.sqrt 2)
  have hdenDeriv :
      HasDerivAt (fun y : ℝ => y ^ 4 + Real.sqrt 2) (4 * x ^ 3) x :=
    hpow.add_const (Real.sqrt 2)
  have hratio := hnumDeriv.div hdenDeriv hden
  have hlog := hratio.log hquot
  have hlogabs :
      HasDerivAt
        (fun y : ℝ =>
          Real.log |(y ^ 4 - Real.sqrt 2) / (y ^ 4 + Real.sqrt 2)|)
        (((4 * x ^ 3) * (x ^ 4 + Real.sqrt 2) -
            (x ^ 4 - Real.sqrt 2) * (4 * x ^ 3)) /
            (x ^ 4 + Real.sqrt 2) ^ 2 /
          ((x ^ 4 - Real.sqrt 2) / (x ^ 4 + Real.sqrt 2))) x := by
    simpa only [Real.log_abs] using hlog
  have hdiff :
      (4 * x ^ 3) * (x ^ 4 + Real.sqrt 2) -
          (x ^ 4 - Real.sqrt 2) * (4 * x ^ 3) =
        8 * Real.sqrt 2 * x ^ 3 := by
    ring
  have hprod :
      (x ^ 4 - Real.sqrt 2) * (x ^ 4 + Real.sqrt 2) = x ^ 8 - 2 := by
    calc
      (x ^ 4 - Real.sqrt 2) * (x ^ 4 + Real.sqrt 2) =
          x ^ 8 - (Real.sqrt 2) ^ 2 := by ring
      _ = x ^ 8 - 2 := by rw [hsqrt_sq]
  have hderivEq :
      1 / (8 * Real.sqrt 2) *
          ((((4 * x ^ 3) * (x ^ 4 + Real.sqrt 2) -
              (x ^ 4 - Real.sqrt 2) * (4 * x ^ 3)) /
              (x ^ 4 + Real.sqrt 2) ^ 2) /
            ((x ^ 4 - Real.sqrt 2) / (x ^ 4 + Real.sqrt 2))) =
        integrand x := by
    rw [hdiff, integrand, ← hprod]
    field_simp [hsqrt_ne, hnum, hden]
  change HasDerivAt
    (fun y : ℝ =>
      1 / (8 * Real.sqrt 2) *
        Real.log |(y ^ 4 - Real.sqrt 2) / (y ^ 4 + Real.sqrt 2)|)
    (integrand x) x
  rw [← hderivEq]
  exact hlogabs.const_mul (1 / (8 * Real.sqrt 2))

theorem gap3 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand s at hF
    change ∃ C, ∀ x ∈ s, F x = primitive x + C
    have hzero : ∀ x ∈ s,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (gap2 x (hdom hx))
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y) s := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ s, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      exact (hzero x hx).deriv
    by_cases hsne : s.Nonempty
    · rcases hsne with ⟨x₀, hx₀⟩
      refine ⟨F x₀ - primitive x₀, ?_⟩
      intro x hx
      have heq : F x - primitive x = F x₀ - primitive x₀ :=
        hopen.is_const_of_deriv_eq_zero hs hdiff hderiv (x := x) hx (y := x₀) hx₀
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact False.elim (hsne ⟨x, hx⟩)
  · rintro ⟨C, hC⟩
    change IsAntiderivativeOn F integrand s
    intro x hx
    have htranslated := (gap2 x (hdom hx)).add_const C
    apply htranslated.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hC y hy

end

end ProofGap.Exercise1679
