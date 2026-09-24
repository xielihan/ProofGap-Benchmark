import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1757

noncomputable section

def domain : Set ℝ := Set.Ioo 0 Real.pi
def original (x : ℝ) : ℝ := Real.cos x ^ 3 / Real.sin x
def factored (x : ℝ) : ℝ :=
  ((1 - Real.sin x ^ 2) / Real.sin x) * Real.cos x
def substituted (x : ℝ) : ℝ :=
  (1 / Real.sin x - Real.sin x) * Real.cos x
def primitive (x : ℝ) : ℝ :=
  Real.log |Real.sin x| - (1 / 2) * Real.sin x ^ 2
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem original_eq_factored_on (x : ℝ) (hx : x ∈ domain) :
    original x = factored x := by
  have htrig : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  unfold original factored
  rw [show Real.cos x ^ 3 / Real.sin x =
      (Real.cos x ^ 2 / Real.sin x) * Real.cos x by ring]
  rw [htrig]

private theorem factored_eq_substituted_on (x : ℝ) (hx : x ∈ domain) :
    factored x = substituted x := by
  have hsin_pos : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hsin_ne : Real.sin x ≠ 0 := ne_of_gt hsin_pos
  unfold factored substituted
  field_simp [hsin_ne]
  <;> ring

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (substituted x) x := by
  have hsin_pos : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hsin_ne : Real.sin x ≠ 0 := ne_of_gt hsin_pos
  have hp :=
    ((Real.hasDerivAt_log hsin_ne).comp x (Real.hasDerivAt_sin x)).sub
      (((Real.hasDerivAt_sin x).pow 2).const_mul (1 / 2))
  rw [show primitive =
      (fun y => Real.log (Real.sin y) - (1 / 2) * Real.sin y ^ 2) by
        funext y
        simp [primitive, Real.log_abs]]
  convert hp using 1 <;> simp [substituted, one_div] <;> ring

private theorem const_on_domain_of_deriv_eq_zero
    {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f domain)
    (hzero : ∀ x ∈ domain, deriv f x = 0) :
    ∀ x ∈ domain, ∀ y ∈ domain, f x = f y := by
  intro x hx y hy
  apply isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (by simpa only [domain] using hf)
      (by simpa only [domain] using hzero)
      hx hy

theorem gap1 : AntiderivativesOn original = AntiderivativesOn factored := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = original x := hderiv x hx
      _ = factored x := original_eq_factored_on x hx
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = factored x := hderiv x hx
      _ = original x := (original_eq_factored_on x hx).symm

theorem gap2 : AntiderivativesOn factored = AntiderivativesOn substituted := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = factored x := hderiv x hx
      _ = substituted x := factored_eq_substituted_on x hx
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = substituted x := hderiv x hx
      _ = factored x := (factored_eq_substituted_on x hx).symm

theorem gap3 : AntiderivativesOn substituted = PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hFd, hFderiv⟩
    have hopen : IsOpen domain := by
      rw [domain]
      exact isOpen_Ioo
    have hHAt : ∀ x ∈ domain,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      have hFa : DifferentiableAt ℝ F x :=
        (hFd x hx).differentiableAt (hopen.mem_nhds hx)
      have hH := hFa.hasDerivAt.sub (primitive_hasDerivAt x hx)
      simpa [hFderiv x hx] using hH
    have hHd : DifferentiableOn ℝ (fun y => F y - primitive y) domain := by
      intro x hx
      exact (hHAt x hx).differentiableAt.differentiableWithinAt
    have hHzero : ∀ x ∈ domain,
        deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      exact (hHAt x hx).deriv
    have hconst := const_on_domain_of_deriv_eq_zero hHd hHzero
    have hb : Real.pi / 2 ∈ domain := by
      rw [domain]
      constructor <;> nlinarith [Real.pi_pos]
    refine ⟨F (Real.pi / 2) - primitive (Real.pi / 2), ?_⟩
    intro x hx
    have heq := hconst x hx (Real.pi / 2) hb
    change F x - primitive x =
      F (Real.pi / 2) - primitive (Real.pi / 2) at heq
    linarith
  · rintro ⟨C, hFC⟩
    have hopen : IsOpen domain := by
      rw [domain]
      exact isOpen_Ioo
    have hFAt : ∀ x ∈ domain, HasDerivAt F (substituted x) x := by
      intro x hx
      have heq : F =ᶠ[nhds x] (fun y => primitive y + C) := by
        filter_upwards [hopen.mem_nhds hx] with y hy
        exact hFC y hy
      exact ((primitive_hasDerivAt x hx).add_const C).congr_of_eventuallyEq heq
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hFAt x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hFAt x hx).deriv

theorem gap4 : AntiderivativesOn original = PrimitiveFamily primitive := by
  exact gap1.trans (gap2.trans gap3)

end
end ProofGap.Exercise1757
