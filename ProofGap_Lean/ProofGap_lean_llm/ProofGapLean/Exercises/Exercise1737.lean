import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1737

noncomputable section

def domain : Set ℝ := Set.Ioi (-2)
def original (x : ℝ) : ℝ := x / ((x + 2) * (x + 3))
def partialFractions (x : ℝ) : ℝ := 3 / (x + 3) - 2 / (x + 2)
def primitive (x : ℝ) : ℝ :=
  Real.log (|x + 3| ^ 3 / (x + 2) ^ 2)
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem primitive_hasDerivAt_on_domain {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt primitive (partialFractions x) x := by
  have hx' : -2 < x := by simpa [domain] using hx
  have hx2 : 0 < x + 2 := by linarith
  have hx3 : 0 < x + 3 := by linarith
  have hx2ne : x + 2 ≠ 0 := ne_of_gt hx2
  have hx3ne : x + 3 ≠ 0 := ne_of_gt hx3
  let q : ℝ → ℝ := fun y =>
    3 * Real.log (y + 3) - 2 * Real.log (y + 2)
  have h3 : HasDerivAt (fun y => 3 * Real.log (y + 3)) (3 / (x + 3)) x := by
    simpa [div_eq_mul_inv] using
      ((((hasDerivAt_id x).add_const (3 : ℝ)).log hx3ne).const_mul (3 : ℝ))
  have h2 : HasDerivAt (fun y => 2 * Real.log (y + 2)) (2 / (x + 2)) x := by
    simpa [div_eq_mul_inv] using
      ((((hasDerivAt_id x).add_const (2 : ℝ)).log hx2ne).const_mul (2 : ℝ))
  have hq : HasDerivAt q (partialFractions x) x := by
    simpa [q, partialFractions] using h3.sub h2
  have hnear : domain ∈ nhds x := by
    exact (show IsOpen domain by
      simpa only [domain] using (isOpen_Ioi : IsOpen (Set.Ioi (-2 : ℝ)))).mem_nhds hx
  have heq : primitive =ᶠ[nhds x] q := by
    filter_upwards [hnear] with y hy
    have hy' : -2 < y := by simpa [domain] using hy
    have hy2 : 0 < y + 2 := by linarith
    have hy3 : 0 < y + 3 := by linarith
    change Real.log (|y + 3| ^ 3 / (y + 2) ^ 2) =
      3 * Real.log (y + 3) - 2 * Real.log (y + 2)
    rw [abs_of_pos hy3]
    rw [Real.log_div (pow_ne_zero _ (ne_of_gt hy3))
      (pow_ne_zero _ (ne_of_gt hy2))]
    rw [Real.log_pow, Real.log_pow]
    norm_num
  exact hq.congr_of_eventuallyEq heq

theorem gap1 : AntiderivativesOn original = AntiderivativesOn partialFractions := by
  have hEq : ∀ x ∈ domain, original x = partialFractions x := by
    intro x hx
    have hx' : -2 < x := by simpa [domain] using hx
    have hx2 : x + 2 ≠ 0 := by linarith
    have hx3 : x + 3 ≠ 0 := by linarith
    unfold original partialFractions
    field_simp [hx2, hx3] <;> ring
  ext F
  constructor
  · rintro ⟨hF, hder⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = original x := hder x hx
      _ = partialFractions x := hEq x hx
  · rintro ⟨hF, hder⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = partialFractions x := hder x hx
      _ = original x := (hEq x hx).symm

theorem gap2 : AntiderivativesOn partialFractions = PrimitiveFamily primitive := by
  ext F
  constructor
  · rintro ⟨hFdiff, hFder⟩
    have hopen : IsOpen domain := by
      simpa only [domain] using (isOpen_Ioi : IsOpen (Set.Ioi (-2 : ℝ)))
    have hd : ∀ x ∈ domain,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt (hopen.mem_nhds hx)
      have hFd : HasDerivAt F (partialFractions x) x := by
        simpa [hFder x hx] using hFat.hasDerivAt
      simpa using hFd.sub (primitive_hasDerivAt_on_domain hx)
    have hd_diff : DifferentiableOn ℝ (fun y => F y - primitive y) domain := by
      intro x hx
      exact (hd x hx).differentiableAt.differentiableWithinAt
    have hpre : IsPreconnected domain := by
      simpa only [domain] using
        (isPreconnected_Ioi : IsPreconnected (Set.Ioi (-2 : ℝ)))
    have hzero : (0 : ℝ) ∈ domain := by norm_num [domain]
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have heq : F x - primitive x = F 0 - primitive 0 :=
      hopen.is_const_of_deriv_eq_zero hpre hd_diff
        (fun z hz => (hd z hz).deriv) hx hzero
    linarith
  · rintro ⟨C, hFC⟩
    have hopen : IsOpen domain := by
      simpa only [domain] using (isOpen_Ioi : IsOpen (Set.Ioi (-2 : ℝ)))
    have hAt : ∀ x ∈ domain, HasDerivAt F (partialFractions x) x := by
      intro x hx
      have hevent : F =ᶠ[nhds x] (fun y => primitive y + C) := by
        filter_upwards [hopen.mem_nhds hx] with y hy
        exact hFC y hy
      exact ((primitive_hasDerivAt_on_domain hx).add_const C).congr_of_eventuallyEq
        hevent
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hAt x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hAt x hx).deriv

theorem gap3 : AntiderivativesOn original = PrimitiveFamily primitive := by
  calc
    AntiderivativesOn original = AntiderivativesOn partialFractions := gap1
    _ = PrimitiveFamily primitive := gap2

end
end ProofGap.Exercise1737
