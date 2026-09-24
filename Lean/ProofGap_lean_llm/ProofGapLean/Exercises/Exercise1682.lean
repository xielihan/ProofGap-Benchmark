import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1682

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / (x * Real.sqrt (x ^ 2 + 1))
def reciprocalAbs (x : ℝ) : ℝ := 1 / |x|
def intermediate (x : ℝ) : ℝ :=
  -Real.log (reciprocalAbs x + Real.sqrt (1 + 1 / x ^ 2))
def primitive (x : ℝ) : ℝ :=
  -Real.log |(1 + Real.sqrt (x ^ 2 + 1)) / x|
def domain : Set ℝ := {x | x ≠ 0}

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem reciprocalAbs_sq (x : ℝ) :
    reciprocalAbs x ^ 2 = 1 / x ^ 2 := by
  unfold reciprocalAbs
  rw [div_pow, one_pow, sq_abs]

private theorem reciprocalAbs_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt reciprocalAbs (-1 / (x * |x|)) x := by
  have hx0 : x ≠ 0 := hx
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
    Real.sqrt (x ^ 2 + 1) = |x| * Real.sqrt (1 + 1 / x ^ 2) := by
  have hx0 : x ≠ 0 := hx
  have halg : x ^ 2 + 1 = x ^ 2 * (1 + 1 / x ^ 2) := by
    field_simp [hx0]
  rw [halg, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs]

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    deriv reciprocalAbs x = -1 / (x * |x|) := by
  exact (reciprocalAbs_hasDerivAt x hx).deriv

theorem gap3 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt intermediate (integrand x) x := by
  have hx0 : x ≠ 0 := hx
  have habs0 : |x| ≠ 0 := abs_ne_zero.mpr hx0
  have hu_pos : 0 < reciprocalAbs x := by
    exact one_div_pos.mpr (abs_pos.mpr hx0)
  have hsarg : 0 < 1 + reciprocalAbs x ^ 2 := by positivity
  have hspos : 0 < Real.sqrt (1 + reciprocalAbs x ^ 2) :=
    Real.sqrt_pos.2 hsarg
  have hs :
      HasDerivAt (fun u : ℝ => Real.sqrt (1 + u ^ 2))
        (reciprocalAbs x / Real.sqrt (1 + reciprocalAbs x ^ 2))
        (reciprocalAbs x) := by
    have hinner :
        HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * reciprocalAbs x)
          (reciprocalAbs x) := by
      convert
        (hasDerivAt_const (reciprocalAbs x) 1).add
          ((hasDerivAt_id (reciprocalAbs x)).pow 2) using 1 <;>
        simp only [id_eq] <;>
        ring
    convert
      (Real.hasDerivAt_sqrt (ne_of_gt hsarg)).comp (reciprocalAbs x) hinner
        using 1 <;>
      field_simp [ne_of_gt hspos] <;>
      ring
  have harg : 0 <
      reciprocalAbs x + Real.sqrt (1 + reciprocalAbs x ^ 2) := by
    linarith
  have houter :
      HasDerivAt
        (fun u : ℝ => -Real.log (u + Real.sqrt (1 + u ^ 2)))
        (-1 / Real.sqrt (1 + reciprocalAbs x ^ 2)) (reciprocalAbs x) := by
    have hsum :=
      (hasDerivAt_id (reciprocalAbs x)).add hs
    have hlog :=
      (Real.hasDerivAt_log (ne_of_gt harg)).comp (reciprocalAbs x) hsum
    convert hlog.neg using 1 <;>
      field_simp [ne_of_gt hspos, ne_of_gt harg] <;>
      ring
  have hcomp :=
    houter.comp x (reciprocalAbs_hasDerivAt x hx)
  convert hcomp using 1
  · funext y
    rw [show ((fun u : ℝ =>
        -Real.log (u + Real.sqrt (1 + u ^ 2))) ∘ reciprocalAbs) y =
          -Real.log (reciprocalAbs y +
            Real.sqrt (1 + reciprocalAbs y ^ 2)) by rfl]
    rw [reciprocalAbs_sq]
    rfl
  · rw [reciprocalAbs_sq]
    unfold integrand
    rw [gap1 x hx]
    field_simp [hx0, habs0,
      ne_of_gt (Real.sqrt_pos.2 (by
        rw [← reciprocalAbs_sq]
        positivity : 0 < 1 + 1 / x ^ 2))]

private theorem intermediate_eq_primitive : intermediate = primitive := by
  funext x
  by_cases hx0 : x = 0
  · subst x
    norm_num [intermediate, primitive, reciprocalAbs]
  · have hx : x ∈ domain := hx0
    have habs0 : |x| ≠ 0 := abs_ne_zero.mpr hx0
    have hnum : 0 < 1 + Real.sqrt (x ^ 2 + 1) := by
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 1)]
    have harg :
        |(1 + Real.sqrt (x ^ 2 + 1)) / x| =
          reciprocalAbs x + Real.sqrt (1 + 1 / x ^ 2) := by
      rw [abs_div, abs_of_pos hnum, gap1 x hx]
      unfold reciprocalAbs
      field_simp [habs0]
    unfold intermediate primitive
    rw [harg]

theorem gap4 (x : ℝ) (hx : x ∈ domain) :
    intermediate x = primitive x := by
  exact congrFun intermediate_eq_primitive x

theorem gap5 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  have hprimitive : ∀ x ∈ s, HasDerivAt primitive (integrand x) x := by
    intro x hx
    rw [← intermediate_eq_primitive]
    exact gap3 x (hdom hx)
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand s at hF
    change ∃ C, ∀ x ∈ s, F x = primitive x + C
    let G : ℝ → ℝ := fun x => F x - primitive x
    have hG : ∀ x ∈ s, HasDerivAt G 0 x := by
      intro x hx
      simpa [G] using (hF x hx).sub (hprimitive x hx)
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
  · rintro ⟨C, hC⟩
    change IsAntiderivativeOn F integrand s
    intro x hx
    have hevent : F =ᶠ[nhds x] fun y => primitive y + C := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact ((hprimitive x hx).add_const C).congr_of_eventuallyEq hevent

end

end ProofGap.Exercise1682
