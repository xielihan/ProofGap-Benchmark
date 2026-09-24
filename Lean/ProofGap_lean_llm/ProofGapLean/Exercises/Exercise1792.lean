import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1792

noncomputable section

def domain : Set ℝ := Set.Ioi 0
def integrand (n x : ℝ) : ℝ := Real.rpow x n * Real.log x
def primitive (n x : ℝ) : ℝ :=
  Real.rpow x (n + 1) / (n + 1) *
    (Real.log x - 1 / (n + 1))
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

theorem gap1 (n x : ℝ) (hn : n ≠ -1) (hx : x ∈ domain) :
    HasDerivAt (fun y => Real.rpow y (n + 1))
      ((n + 1) * Real.rpow x n) x := by
  change 0 < x at hx
  have h := Real.hasDerivAt_rpow_const (p := n + 1)
    (Or.inl (ne_of_gt hx))
  have hexp : n + 1 - 1 = n := by ring
  rw [hexp] at h
  change HasDerivAt (fun y => y ^ (n + 1)) ((n + 1) * x ^ n) x
  exact h

theorem gap2 (n x : ℝ) (hn : n ≠ -1) (hx : x ∈ domain) :
    HasDerivAt
      (fun y =>
        Real.rpow y (n + 1) / (n + 1) * Real.log y -
          Real.rpow y (n + 1) / (n + 1) ^ 2)
      (integrand n x) x := by
  have hxd : x ∈ domain := hx
  change 0 < x at hx
  have hne : n + 1 ≠ 0 := by
    intro h
    apply hn
    linarith
  have hxne : x ≠ 0 := ne_of_gt hx
  have hpow : Real.rpow x (n + 1) = Real.rpow x n * x := by
    simpa using (Real.rpow_add hx n (1 : ℝ))
  have hp := gap1 n x hn hxd
  have hfirst := (hp.div_const (n + 1)).mul (Real.hasDerivAt_log hxne)
  have hsecond := hp.div_const ((n + 1) ^ 2)
  convert hfirst.sub hsecond using 1
  unfold integrand
  rw [hpow]
  field_simp [hne, hxne]
  <;> ring

theorem gap3 (n x : ℝ) (hn : n ≠ -1) (hx : x ∈ domain) :
    Real.rpow x (n + 1) / (n + 1) * Real.log x -
        Real.rpow x (n + 1) / (n + 1) ^ 2 =
      primitive n x := by
  have hne : n + 1 ≠ 0 := by
    intro h
    apply hn
    linarith
  unfold primitive
  field_simp [hne]
  <;> ring

theorem gap4 (n : ℝ) (hn : n ≠ -1) :
    Family (integrand n) domain = Translates (primitive n) domain := by
  have hne : n + 1 ≠ 0 := by
    intro h
    apply hn
    linarith
  have hformula :
      (fun y =>
        Real.rpow y (n + 1) / (n + 1) * Real.log y -
          Real.rpow y (n + 1) / (n + 1) ^ 2) = primitive n := by
    funext y
    unfold primitive
    field_simp [hne]
    <;> ring
  have hprimitive : IsAntiderivativeOn (primitive n) (integrand n) domain := by
    intro x hx
    rw [← hformula]
    exact gap2 n x hn hx
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F (integrand n) domain at hF
    change ∃ C, ∀ x ∈ domain, F x = primitive n x + C
    have hzero :
        ∀ x ∈ domain,
          HasDerivAt (fun y => F y - primitive n y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (hprimitive x hx)
    have hcomp :
        ∀ t : ℝ,
          HasDerivAt
            (fun u => F (Real.exp u) - primitive n (Real.exp u)) 0 t := by
      intro t
      have ht : Real.exp t ∈ domain := by
        change 0 < Real.exp t
        exact Real.exp_pos t
      simpa using
        ((hzero (Real.exp t) ht).comp t (Real.hasDerivAt_exp t))
    have hdiff :
        Differentiable ℝ
          (fun u => F (Real.exp u) - primitive n (Real.exp u)) := by
      intro t
      exact (hcomp t).differentiableAt
    have hderiv :
        ∀ t : ℝ,
          deriv (fun u => F (Real.exp u) - primitive n (Real.exp u)) t = 0 := by
      intro t
      exact (hcomp t).deriv
    have hconst := is_const_of_deriv_eq_zero hdiff hderiv
    refine ⟨F 1 - primitive n 1, ?_⟩
    intro x hx
    have hxpos : 0 < x := by
      exact hx
    have hc := hconst (Real.log x) 0
    have hc' : F x - primitive n x = F 1 - primitive n 1 := by
      simpa [Real.exp_log hxpos] using hc
    linarith
  · intro hF
    change ∃ C, ∀ x ∈ domain, F x = primitive n x + C at hF
    change IsAntiderivativeOn F (integrand n) domain
    rcases hF with ⟨C, hC⟩
    intro x hx
    have hder := (hprimitive x hx).add_const C
    apply hder.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact hC y hy

end

end ProofGap.Exercise1792
