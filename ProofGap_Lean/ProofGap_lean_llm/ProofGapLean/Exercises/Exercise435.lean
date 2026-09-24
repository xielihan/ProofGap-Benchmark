import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise435

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.sqrt (x + Real.sqrt (x + Real.sqrt x)) / Real.sqrt (x + 1)
def normalized (x : ℝ) : ℝ :=
  Real.sqrt (1 + Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3))) /
    Real.sqrt (1 + 1 / x)
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, N < x → |f x - L| < ε

/-- Exercise 435, gap 1. -/
theorem gap1 :
    HasLimitAtPosInfinity original 1 ↔ HasLimitAtPosInfinity normalized 1 := by
  have hEq : ∀ x : ℝ, 0 < x → original x = normalized x := by
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    have hxne : x ≠ 0 := ne_of_gt hx
    have hinv3 : 0 ≤ 1 / x ^ 3 := by positivity
    have hs3 : (Real.sqrt (1 / x ^ 3)) ^ 2 = 1 / x ^ 3 :=
      Real.sq_sqrt hinv3
    have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0
    have hscaledSq :
        (x ^ 2 * Real.sqrt (1 / x ^ 3)) ^ 2 = x := by
      rw [mul_pow, hs3]
      field_simp [hxne]
    have hscaledNonneg :
        0 ≤ x ^ 2 * Real.sqrt (1 / x ^ 3) :=
      mul_nonneg (sq_nonneg x) (Real.sqrt_nonneg _)
    set y : ℝ := x ^ 2 * Real.sqrt (1 / x ^ 3) with hy
    have hySq : y ^ 2 = x := by
      simpa [hy] using hscaledSq
    have hyNonneg : 0 ≤ y := by
      simpa [hy] using hscaledNonneg
    have hySqrt : y = Real.sqrt x := by
      nlinarith only [hySq, hsx, hyNonneg, Real.sqrt_nonneg x]
    have hscale :
        x ^ 2 * Real.sqrt (1 / x ^ 3) = Real.sqrt x := by
      simpa [hy] using hySqrt
    have hc :
        0 ≤ 1 / x + Real.sqrt (1 / x ^ 3) := by positivity
    have hcsq :
        (Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3))) ^ 2 =
          1 / x + Real.sqrt (1 / x ^ 3) :=
      Real.sq_sqrt hc
    have hfirst : x ^ 2 * (1 / x) = x := by
      field_simp [hxne]
    have hrightSq :
        (x * Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3))) ^ 2 =
          x + Real.sqrt x := by
      calc
        (x * Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3))) ^ 2 =
            x ^ 2 * (Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3))) ^ 2 := by
              ring
        _ = x ^ 2 * (1 / x + Real.sqrt (1 / x ^ 3)) := by rw [hcsq]
        _ = x ^ 2 * (1 / x) + x ^ 2 * Real.sqrt (1 / x ^ 3) := by ring
        _ = x + Real.sqrt x := by rw [hfirst, hscale]
    have hrightNonneg :
        0 ≤ x * Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3)) :=
      mul_nonneg hx0 (Real.sqrt_nonneg _)
    have hinnerSq :
        (Real.sqrt (x + Real.sqrt x)) ^ 2 = x + Real.sqrt x :=
      Real.sq_sqrt (add_nonneg hx0 (Real.sqrt_nonneg _))
    set z : ℝ := x * Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3)) with hz
    have hzSq : z ^ 2 = x + Real.sqrt x := by
      simpa [hz] using hrightSq
    have hzNonneg : 0 ≤ z := by
      simpa [hz] using hrightNonneg
    have hinnerZ : Real.sqrt (x + Real.sqrt x) = z := by
      nlinarith only [hzSq, hinnerSq, hzNonneg,
        Real.sqrt_nonneg (x + Real.sqrt x)]
    have hinner :
        Real.sqrt (x + Real.sqrt x) =
          x * Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3)) := by
      simpa [hz] using hinnerZ
    have hrad :
        x + Real.sqrt (x + Real.sqrt x) =
          x * (1 + Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3))) := by
      rw [hinner]
      ring
    have hnum :
        Real.sqrt (x + Real.sqrt (x + Real.sqrt x)) =
          Real.sqrt x *
            Real.sqrt (1 + Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3))) := by
      rw [hrad]
      exact Real.sqrt_mul hx0 _
    have hdenrad : x + 1 = x * (1 + 1 / x) := by
      field_simp [hxne]
    have hden :
        Real.sqrt (x + 1) = Real.sqrt x * Real.sqrt (1 + 1 / x) := by
      rw [hdenrad]
      exact Real.sqrt_mul hx0 _
    have hsxne : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
    have hdpos : 0 < Real.sqrt (1 + 1 / x) :=
      Real.sqrt_pos.2 (by positivity)
    have hdne : Real.sqrt (1 + 1 / x) ≠ 0 := ne_of_gt hdpos
    unfold original normalized
    rw [hnum, hden]
    field_simp [hsxne, hdne]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨N, hN, hlim⟩
    refine ⟨N, hN, ?_⟩
    intro x hx
    rw [← hEq x (lt_trans hN hx)]
    exact hlim x hx
  · intro h ε hε
    rcases h ε hε with ⟨N, hN, hlim⟩
    refine ⟨N, hN, ?_⟩
    intro x hx
    rw [hEq x (lt_trans hN hx)]
    exact hlim x hx

/-- Exercise 435, gap 2. -/
theorem gap2 : HasLimitAtPosInfinity normalized 1 := by
  have hinv :
      Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))
  have hinv3 :
      Filter.Tendsto (fun x : ℝ => 1 / x ^ 3) Filter.atTop (nhds 0) := by
    simpa [one_div] using hinv.pow 3
  have hsqrt3 :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 / x ^ 3))
        Filter.atTop (nhds 0) := by
    convert
      (Real.continuous_sqrt.continuousAt.tendsto.comp hinv3) using 1 <;>
      simp only [Function.comp_apply, Real.sqrt_zero]
  have hinnerArg :
      Filter.Tendsto
        (fun x : ℝ => 1 / x + Real.sqrt (1 / x ^ 3))
        Filter.atTop (nhds 0) := by
    simpa only [add_zero] using hinv.add hsqrt3
  have hinner :
      Filter.Tendsto
        (fun x : ℝ => Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3)))
        Filter.atTop (nhds 0) := by
    convert
      (Real.continuous_sqrt.continuousAt.tendsto.comp hinnerArg) using 1 <;>
      simp only [Function.comp_apply, Real.sqrt_zero]
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have hnumArg :
      Filter.Tendsto
        (fun x : ℝ => 1 + Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3)))
        Filter.atTop (nhds 1) := by
    simpa only [add_zero] using hone.add hinner
  have hnum :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.sqrt (1 + Real.sqrt (1 / x + Real.sqrt (1 / x ^ 3))))
        Filter.atTop (nhds 1) := by
    convert
      (Real.continuous_sqrt.continuousAt.tendsto.comp hnumArg) using 1 <;>
      simp only [Function.comp_apply, Real.sqrt_one]
  have hdenArg :
      Filter.Tendsto (fun x : ℝ => 1 + 1 / x)
        Filter.atTop (nhds 1) := by
    simpa only [add_zero] using hone.add hinv
  have hden :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 + 1 / x))
        Filter.atTop (nhds 1) := by
    convert
      (Real.continuous_sqrt.continuousAt.tendsto.comp hdenArg) using 1 <;>
      simp only [Function.comp_apply, Real.sqrt_one]
  have hlim :
      Filter.Tendsto normalized Filter.atTop (nhds 1) := by
    unfold normalized
    simpa only [div_one] using
      hnum.div hden (one_ne_zero : (1 : ℝ) ≠ 0)
  intro ε hε
  have hev :
      ∀ᶠ x : ℝ in Filter.atTop, dist (normalized x) 1 < ε :=
    (Metric.tendsto_nhds.1 hlim) ε hε
  rcases (Filter.eventually_atTop.1 hev) with ⟨N, hN⟩
  refine ⟨max N 1, lt_of_lt_of_le zero_lt_one (le_max_right N 1), ?_⟩
  intro x hx
  have hxN : N ≤ x :=
    le_trans (le_max_left N 1) (le_of_lt hx)
  simpa [Real.dist_eq] using hN x hxN

/-- Exercise 435, gap 3. -/
theorem gap3 : HasLimitAtPosInfinity original 1 := by
  exact gap1.mpr gap2

end

end ProofGap.Exercise435
