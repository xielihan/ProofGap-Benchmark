import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1683

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / (x * Real.sqrt (x ^ 2 - 1))
def reciprocalAbs (x : ℝ) : ℝ := 1 / |x|
def primitive (x : ℝ) : ℝ := -Real.arcsin (reciprocalAbs x)
def domain : Set ℝ := {x | 1 < |x|}

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem reciprocalAbs_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt reciprocalAbs (-1 / (x * |x|)) x := by
  have hxabs : 1 < |x| := hx
  have habspos : 0 < |x| := lt_trans zero_lt_one hxabs
  have hx0 : x ≠ 0 := abs_pos.mp habspos
  rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
  · have hbase : HasDerivAt (fun y : ℝ => (-y)⁻¹)
        (-(-1 : ℝ) / (-x) ^ 2) x := by
      simpa using (hasDerivAt_id x).neg.inv (neg_ne_zero.mpr hx0)
    have hev : reciprocalAbs =ᶠ[nhds x] fun y : ℝ => (-y)⁻¹ := by
      filter_upwards [Iio_mem_nhds hxneg] with y hy
      have hy' : y < 0 := hy
      simp [reciprocalAbs, abs_of_neg hy']
    have hrec : HasDerivAt reciprocalAbs (-(-1 : ℝ) / (-x) ^ 2) x :=
      hbase.congr_of_eventuallyEq hev
    have hcoef : -(-1 : ℝ) / (-x) ^ 2 = -1 / (x * |x|) := by
      rw [abs_of_neg hxneg]
      field_simp [hx0]
      <;> ring
    rw [hcoef] at hrec
    exact hrec
  · have hbase : HasDerivAt (fun y : ℝ => y⁻¹) (-1 / x ^ 2) x := by
      simpa using (hasDerivAt_id x).inv hx0
    have hev : reciprocalAbs =ᶠ[nhds x] fun y : ℝ => y⁻¹ := by
      filter_upwards [Ioi_mem_nhds hxpos] with y hy
      have hy' : 0 < y := hy
      simp [reciprocalAbs, abs_of_pos hy']
    have hrec : HasDerivAt reciprocalAbs (-1 / x ^ 2) x :=
      hbase.congr_of_eventuallyEq hev
    have hcoef : -1 / x ^ 2 = -1 / (x * |x|) := by
      rw [abs_of_pos hxpos]
      field_simp [hx0]
      <;> ring
    rw [hcoef] at hrec
    exact hrec

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    Real.sqrt (x ^ 2 - 1) = |x| * Real.sqrt (1 - 1 / x ^ 2) := by
  have hxabs : 1 < |x| := hx
  have habspos : 0 < |x| := lt_trans zero_lt_one hxabs
  have hx0 : x ≠ 0 := abs_pos.mp habspos
  have halg : x ^ 2 - 1 = x ^ 2 * (1 - 1 / x ^ 2) := by
    field_simp [hx0]
    <;> ring
  rw [halg, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs]

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    deriv reciprocalAbs x = -1 / (x * |x|) := by
  exact (reciprocalAbs_hasDerivAt x hx).deriv

theorem gap3 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have hxabs : 1 < |x| := hx
  have habspos : 0 < |x| := lt_trans zero_lt_one hxabs
  have hx0 : x ≠ 0 := abs_pos.mp habspos
  have habs0 : |x| ≠ 0 := ne_of_gt habspos
  have hu_pos : 0 < reciprocalAbs x := by
    exact one_div_pos.mpr habspos
  have hu_lt : reciprocalAbs x < 1 := by
    unfold reciprocalAbs
    exact (div_lt_one habspos).2 hxabs
  have hu : reciprocalAbs x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hu_lt⟩
  have hu_sq : reciprocalAbs x ^ 2 = 1 / x ^ 2 := by
    unfold reciprocalAbs
    field_simp [hx0, habs0]
    <;> nlinarith [sq_abs x]
  have hsarg : 0 < 1 - 1 / x ^ 2 := by
    rw [← hu_sq]
    nlinarith
  have hsqrt : Real.sqrt (1 - 1 / x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hsarg)
  have harc :=
    (Real.hasDerivAt_arcsin (ne_of_gt hu.1) (ne_of_lt hu.2)).comp x
      (reciprocalAbs_hasDerivAt x hx)
  have hneg := harc.neg
  have hcoef :
      -((1 / Real.sqrt (1 - reciprocalAbs x ^ 2)) *
          (-1 / (x * |x|))) = integrand x := by
    rw [hu_sq]
    unfold integrand
    rw [gap1 x hx]
    field_simp [hx0, habs0, hsqrt]
    <;> ring
  rw [hcoef] at hneg
  simpa [primitive] using hneg

theorem gap4 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand s at hF
    change ∃ C, ∀ x ∈ s, F x = primitive x + C
    let G : ℝ → ℝ := fun x => F x - primitive x
    have hG : ∀ x ∈ s, HasDerivAt G 0 x := by
      intro x hx
      simpa [G] using (hF x hx).sub (gap3 x (hdom hx))
    have hGdiff : DifferentiableOn ℝ G s := by
      intro x hx
      exact (hG x hx).differentiableAt.differentiableWithinAt
    have hGderiv : ∀ x ∈ s, deriv G x = 0 := by
      intro x hx
      exact (hG x hx).deriv
    by_cases hne : s.Nonempty
    · rcases hne with ⟨x₀, hx₀⟩
      refine ⟨G x₀, ?_⟩
      intro x hx
      have heq : G x = G x₀ :=
        hopen.is_const_of_deriv_eq_zero hs hGdiff hGderiv hx hx₀
      dsimp [G] at heq ⊢
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact False.elim (hne ⟨x, hx⟩)
  · intro hF
    change (∃ C, ∀ x ∈ s, F x = primitive x + C) at hF
    rcases hF with ⟨C, hC⟩
    change IsAntiderivativeOn F integrand s
    intro x hx
    have hevent : F =ᶠ[nhds x] fun y => primitive y + C := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    have hderiv : HasDerivAt (fun y => primitive y + C) (integrand x) x := by
      simpa using (gap3 x (hdom hx)).add_const C
    exact hderiv.congr_of_eventuallyEq hevent

end

end ProofGap.Exercise1683
