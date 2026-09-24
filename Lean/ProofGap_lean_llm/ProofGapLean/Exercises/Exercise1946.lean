import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue

namespace ProofGap.Exercise1946

noncomputable section

def q (x : ℝ) := x ^ 2 + 4 * x + 3
def branch : Set ℝ := {x | 0 < q x}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def BranchwisePrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ u : Set ℝ, IsOpen u → IsPreconnected u → u ⊆ s →
    ∃ C : ℝ, ∀ x ∈ u, F x = p x + C}
def polynomialRhs (a b c lam x : ℝ) :=
  (2 * a * x + b) * q x + (x + 2) * (a * x ^ 2 + b * x + c) + lam
def CoeffIdentity (a b c lam : ℝ) : Prop :=
  ∀ x, x ^ 3 - 6 * x ^ 2 + 11 * x - 6 = polynomialRhs a b c lam x
def integrand (x : ℝ) :=
  (x ^ 3 - 6 * x ^ 2 + 11 * x - 6) / Real.sqrt (q x)
def primitive (x : ℝ) :=
  (1 / 3 * x ^ 2 - 14 / 3 * x + 37) * Real.sqrt (q x) -
    66 * Real.log |x + 2 + Real.sqrt (q x)|

private theorem eq_of_hasDerivAt_zero_on_Icc {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hcont : ContinuousOn f (Set.Icc a b))
    (hzero : ∀ x ∈ Set.Ioo a b, HasDerivAt f 0 x) : f a = f b := by
  rcases exists_hasDerivAt_eq_slope f (fun _ : ℝ => (0 : ℝ)) hab hcont hzero with
    ⟨x, hx, hslope⟩
  have hslope0 : (f b - f a) / (b - a) = 0 := hslope.symm
  have hden : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  field_simp [hden] at hslope0
  have hslope1 : f b - f a = 0 := by
    simpa using hslope0
  exact (sub_eq_zero.mp hslope1).symm

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (integrand x) x := by
  change 0 < q x at hx
  have hspos : 0 < Real.sqrt (q x) := Real.sqrt_pos.2 hx
  have hsne : Real.sqrt (q x) ≠ 0 := ne_of_gt hspos
  have hsq : (Real.sqrt (q x)) ^ 2 = q x := Real.sq_sqrt (le_of_lt hx)
  have hq : HasDerivAt q (2 * x + 4) x := by
    convert ((((hasDerivAt_id x).pow 2).add
      ((hasDerivAt_const x (4 : ℝ)).mul (hasDerivAt_id x))).add_const 3) using 1 <;>
      simp <;> ring
  have hs : HasDerivAt (fun y => Real.sqrt (q y))
      ((x + 2) / Real.sqrt (q x)) x := by
    have ht := (Real.hasDerivAt_sqrt (ne_of_gt hx)).comp x hq
    convert ht using 1
    field_simp [hsne]
    ring
  have hz : x + 2 + Real.sqrt (q x) ≠ 0 := by
    intro hz0
    have hqform : q x = (x + 2) ^ 2 - 1 := by
      unfold q
      ring
    nlinarith
  have hzder : HasDerivAt
      (fun y => y + 2 + Real.sqrt (q y))
      (1 + (x + 2) / Real.sqrt (q x)) x := by
    exact ((hasDerivAt_id x).add_const 2).add hs
  have hlog : HasDerivAt
      (fun y => Real.log |y + 2 + Real.sqrt (q y)|)
      (1 / Real.sqrt (q x)) x := by
    have ht := (Real.hasDerivAt_log hz).comp x hzder
    convert ht using 1
    · funext y
      simp only [Function.comp_apply, Real.log_abs]
    · field_simp [hsne, hz]
      ring
  have hp : HasDerivAt
      (fun y : ℝ => 1 / 3 * y ^ 2 - 14 / 3 * y + 37)
      (2 / 3 * x - 14 / 3) x := by
    have hterm1 := (hasDerivAt_const x (1 / 3 : ℝ)).mul
      ((hasDerivAt_id x).pow 2)
    have hterm2 := (hasDerivAt_const x (14 / 3 : ℝ)).mul
      (hasDerivAt_id x)
    convert ((hterm1.sub hterm2).add_const 37) using 1 <;>
      simp <;> ring
  have hprod := hp.mul hs
  have hlogmul : HasDerivAt
      (fun y => 66 * Real.log |y + 2 + Real.sqrt (q y)|)
      (66 * (1 / Real.sqrt (q x))) x := by
    convert (hasDerivAt_const x (66 : ℝ)).mul hlog using 1 <;>
      simp
  convert (hprod.sub hlogmul) using 1
  unfold integrand
  have hid : x ^ 3 - 6 * x ^ 2 + 11 * x - 6 =
      polynomialRhs (1 / 3) (-14 / 3) 37 (-66) x := by
    unfold polynomialRhs q
    ring
  rw [hid]
  unfold polynomialRhs
  field_simp [hsne]
  rw [hsq]
  ring

theorem gap1 :
    ∃ a b c lam : ℝ, CoeffIdentity a b c lam := by
  refine ⟨1 / 3, -14 / 3, 37, -66, ?_⟩
  intro x
  unfold polynomialRhs q
  ring
theorem gap2 (a b c lam : ℝ) (h : CoeffIdentity a b c lam) :
    a = 1 / 3 := by
  have h0 := h 0
  have h1 := h (-1)
  have h2 := h (-2)
  have h3 := h (-3)
  norm_num [CoeffIdentity, polynomialRhs, q] at h0 h1 h2 h3
  linarith
theorem gap3 (a b c lam : ℝ) (h : CoeffIdentity a b c lam) :
    b = -14 / 3 := by
  have h0 := h 0
  have h1 := h (-1)
  have h2 := h (-2)
  have h3 := h (-3)
  norm_num [CoeffIdentity, polynomialRhs, q] at h0 h1 h2 h3
  linarith
theorem gap4 (a b c lam : ℝ) (h : CoeffIdentity a b c lam) :
    c = 37 := by
  have h0 := h 0
  have h1 := h (-1)
  have h2 := h (-2)
  have h3 := h (-3)
  norm_num [CoeffIdentity, polynomialRhs, q] at h0 h1 h2 h3
  linarith
theorem gap5 (a b c lam : ℝ) (h : CoeffIdentity a b c lam) :
    lam = -66 := by
  have h0 := h 0
  have h1 := h (-1)
  have h2 := h (-2)
  have h3 := h (-3)
  norm_num [CoeffIdentity, polynomialRhs, q] at h0 h1 h2 h3
  linarith
theorem gap6 :
    AntiderivativesOn branch integrand =
      BranchwisePrimitiveFamilyOn branch primitive := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ u : Set ℝ, IsOpen u → IsPreconnected u → u ⊆ branch →
      ∃ C : ℝ, ∀ x ∈ u, F x = primitive x + C
    intro u huopen huconn husub
    by_cases hune : u.Nonempty
    · rcases hune with ⟨x₀, hx₀⟩
      refine ⟨F x₀ - primitive x₀, ?_⟩
      have hd (y : ℝ) (hy : y ∈ u) :
          HasDerivAt (fun z => F z - primitive z) 0 y := by
        simpa only [Pi.sub_apply, sub_self] using
          (hF y (husub hy)).sub (primitive_hasDerivAt y (husub hy))
      have hcont : ContinuousOn (fun y => F y - primitive y) u := by
        intro y hy
        exact (hd y hy).continuousAt.continuousWithinAt
      have huord : Set.OrdConnected u :=
        isPreconnected_iff_ordConnected.mp huconn
      intro x hx
      have heq : F x - primitive x = F x₀ - primitive x₀ := by
        rcases lt_trichotomy x x₀ with hlt | heq | hgt
        · have hsub : Set.Icc x x₀ ⊆ u := huord.out hx hx₀
          exact eq_of_hasDerivAt_zero_on_Icc hlt
            (hcont.mono hsub)
            (fun y hy => hd y (hsub ⟨le_of_lt hy.1, le_of_lt hy.2⟩))
        · subst x
          rfl
        · have hsub : Set.Icc x₀ x ⊆ u := huord.out hx₀ hx
          exact (eq_of_hasDerivAt_zero_on_Icc hgt
            (hcont.mono hsub)
            (fun y hy => hd y (hsub ⟨le_of_lt hy.1, le_of_lt hy.2⟩))).symm
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact False.elim (hune ⟨x, hx⟩)
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    have hxq : 0 < q x := hx
    have hqx : q x = (x + 1) * (x + 3) := by
      unfold q
      ring
    have hcases : x < -3 ∨ -1 < x := by
      rcases lt_or_ge x (-2) with hx2 | hx2
      · left
        by_contra hn
        have hx3 : -3 ≤ x := le_of_not_gt hn
        have hp : (x + 1) * (x + 3) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        rw [hqx] at hxq
        linarith
      · right
        by_contra hn
        have hx1 : x ≤ -1 := le_of_not_gt hn
        have hp : (x + 1) * (x + 3) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        rw [hqx] at hxq
        linarith
    rcases hcases with hxleft | hxright
    · have hsub : Set.Iio (-3 : ℝ) ⊆ branch := by
        intro y hy
        change y < -3 at hy
        change 0 < q y
        have hfac : q y = (y + 1) * (y + 3) := by
          unfold q
          ring
        rw [hfac]
        exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
      rcases hF (Set.Iio (-3 : ℝ)) isOpen_Iio isPreconnected_Iio hsub with ⟨C, hC⟩
      have hp := (primitive_hasDerivAt x hx).add_const C
      apply hp.congr_of_eventuallyEq
      have hxmem : x ∈ Set.Iio (-3 : ℝ) := hxleft
      filter_upwards [isOpen_Iio.mem_nhds hxmem] with y hy
      exact hC y hy
    · have hsub : Set.Ioi (-1 : ℝ) ⊆ branch := by
        intro y hy
        change -1 < y at hy
        change 0 < q y
        have hfac : q y = (y + 1) * (y + 3) := by
          unfold q
          ring
        rw [hfac]
        exact mul_pos (by linarith) (by linarith)
      rcases hF (Set.Ioi (-1 : ℝ)) isOpen_Ioi isPreconnected_Ioi hsub with ⟨C, hC⟩
      have hp := (primitive_hasDerivAt x hx).add_const C
      apply hp.congr_of_eventuallyEq
      have hxmem : x ∈ Set.Ioi (-1 : ℝ) := hxright
      filter_upwards [isOpen_Ioi.mem_nhds hxmem] with y hy
      exact hC y hy

end
end ProofGap.Exercise1946
