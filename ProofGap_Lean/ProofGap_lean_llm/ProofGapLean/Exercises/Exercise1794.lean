import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1794

noncomputable section

def domain : Set ℝ := Set.Ioi 0
def integrand (x : ℝ) : ℝ := Real.sqrt x * Real.log x ^ 2
def primitive (x : ℝ) : ℝ :=
  (2 / 3 : ℝ) * Real.sqrt x ^ 3 *
    (Real.log x ^ 2 - (4 / 3 : ℝ) * Real.log x + 8 / 9)
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt (fun y => Real.sqrt y ^ 3)
      ((3 / 2 : ℝ) * Real.sqrt x) x := by
  have hxpos : 0 < x := hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hs0 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hxpos).ne'
  convert (Real.hasDerivAt_sqrt hx0).pow 3 using 1 <;>
    field_simp [hs0] <;> ring

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt
      (fun y => (2 / 3 : ℝ) * Real.sqrt y ^ 3 * Real.log y ^ 2)
      (integrand x + (4 / 3 : ℝ) * Real.sqrt x * Real.log x) x := by
  have hxpos : 0 < x := hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hsqx : Real.sqrt x ^ 2 = x := Real.sq_sqrt (le_of_lt hxpos)
  have hcube : Real.sqrt x ^ 3 = Real.sqrt x * x := by
    calc
      Real.sqrt x ^ 3 = Real.sqrt x * Real.sqrt x ^ 2 := by ring
      _ = Real.sqrt x * x := by rw [hsqx]
  have h :=
    ((gap1 x hx).const_mul (2 / 3 : ℝ)).mul
      ((Real.hasDerivAt_log hx0).pow 2)
  convert h using 1
  rw [hcube]
  simp only [integrand, Pi.pow_apply]
  field_simp [hx0]
  ring

theorem gap3 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt
      (fun y => (8 / 9 : ℝ) * Real.sqrt y ^ 3 * Real.log y)
      ((4 / 3 : ℝ) * Real.sqrt x * Real.log x +
        (8 / 9 : ℝ) * Real.sqrt x) x := by
  have hxpos : 0 < x := hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hsqx : Real.sqrt x ^ 2 = x := Real.sq_sqrt (le_of_lt hxpos)
  have hcube : Real.sqrt x ^ 3 = Real.sqrt x * x := by
    calc
      Real.sqrt x ^ 3 = Real.sqrt x * Real.sqrt x ^ 2 := by ring
      _ = Real.sqrt x * x := by rw [hsqx]
  have h :=
    ((gap1 x hx).const_mul (8 / 9 : ℝ)).mul
      (Real.hasDerivAt_log hx0)
  convert h using 1
  rw [hcube]
  field_simp [hx0] <;> ring

theorem gap4 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt
      (fun y => (16 / 27 : ℝ) * Real.sqrt y ^ 3)
      ((8 / 9 : ℝ) * Real.sqrt x) x := by
  convert (gap1 x hx).const_mul (16 / 27 : ℝ) using 1 <;> ring

theorem gap5 (x : ℝ) (hx : x ∈ domain) :
    (2 / 3 : ℝ) * Real.sqrt x ^ 3 * Real.log x ^ 2 -
          (8 / 9 : ℝ) * Real.sqrt x ^ 3 * Real.log x +
          (16 / 27 : ℝ) * Real.sqrt x ^ 3 =
      primitive x := by
  unfold primitive
  ring

theorem gap6 :
    Family integrand domain = Translates primitive domain := by
  have hfun :
      primitive = fun y =>
        (2 / 3 : ℝ) * Real.sqrt y ^ 3 * Real.log y ^ 2 -
          (8 / 9 : ℝ) * Real.sqrt y ^ 3 * Real.log y +
          (16 / 27 : ℝ) * Real.sqrt y ^ 3 := by
    funext y
    unfold primitive
    ring
  have hprim : ∀ x ∈ domain, HasDerivAt primitive (integrand x) x := by
    intro x hx
    have h := ((gap2 x hx).sub (gap3 x hx)).add (gap4 x hx)
    rw [hfun]
    convert h using 1 <;> ring
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand domain at hF
    change ∃ C, ∀ x ∈ domain, F x = primitive x + C
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have hxpos : 0 < x := hx
    let G : ℝ → ℝ := fun t => F (Real.exp t) - primitive (Real.exp t)
    have hG : ∀ t, HasDerivAt G 0 t := by
      intro t
      have ht : Real.exp t ∈ domain := Real.exp_pos t
      have hd := (hF (Real.exp t) ht).sub (hprim (Real.exp t) ht)
      have hc := hd.comp t (Real.hasDerivAt_exp t)
      simpa [G] using hc
    have hGdiff : Differentiable ℝ G := by
      intro t
      exact (hG t).differentiableAt
    have hGderiv : ∀ t, deriv G t = 0 := by
      intro t
      exact (hG t).deriv
    have hc : G (Real.log x) = G 0 :=
      (is_const_of_deriv_eq_zero hGdiff hGderiv) (Real.log x) 0
    dsimp [G] at hc
    rw [Real.exp_log hxpos, Real.exp_zero] at hc
    linarith
  · intro hF
    change ∃ C, ∀ x ∈ domain, F x = primitive x + C at hF
    rcases hF with ⟨C, hC⟩
    change IsAntiderivativeOn F integrand domain
    intro x hx
    have hpC :
        HasDerivAt (fun y => primitive y + C) (integrand x) x := by
      simpa using (hprim x hx).add_const C
    apply hpC.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact hC y hy

end

end ProofGap.Exercise1794
