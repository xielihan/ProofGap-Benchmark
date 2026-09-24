import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise436

noncomputable section

def original (x : ℝ) : ℝ :=
  (Real.sqrt x + Real.rpow x (1 / 3 : ℝ) + Real.rpow x (1 / 4 : ℝ)) /
    Real.sqrt (2 * x + 1)
def normalized (x : ℝ) : ℝ :=
  (1 + Real.rpow x (-1 / 6 : ℝ) + Real.rpow x (-1 / 4 : ℝ)) /
    Real.sqrt (2 + 1 / x)
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, N < x → |f x - L| < ε

/-- Exercise 436, gap 1. -/
theorem gap1 :
    HasLimitAtPosInfinity original (1 / Real.sqrt 2) ↔
      HasLimitAtPosInfinity normalized (1 / Real.sqrt 2) := by
  have hEq : ∀ x : ℝ, 0 < x → original x = normalized x := by
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    have hxne : x ≠ 0 := ne_of_gt hx
    have hsqrt : Real.sqrt x = Real.rpow x (1 / 2 : ℝ) :=
      Real.sqrt_eq_rpow x
    have hmul13 :
        Real.sqrt x * Real.rpow x (-1 / 6 : ℝ) =
          Real.rpow x (1 / 3 : ℝ) := by
      rw [hsqrt]
      calc
        Real.rpow x (1 / 2 : ℝ) * Real.rpow x (-1 / 6 : ℝ) =
            Real.rpow x ((1 / 2 : ℝ) + (-1 / 6 : ℝ)) :=
          (Real.rpow_add hx _ _).symm
        _ = Real.rpow x (1 / 3 : ℝ) := by norm_num
    have hmul14 :
        Real.sqrt x * Real.rpow x (-1 / 4 : ℝ) =
          Real.rpow x (1 / 4 : ℝ) := by
      rw [hsqrt]
      calc
        Real.rpow x (1 / 2 : ℝ) * Real.rpow x (-1 / 4 : ℝ) =
            Real.rpow x ((1 / 2 : ℝ) + (-1 / 4 : ℝ)) :=
          (Real.rpow_add hx _ _).symm
        _ = Real.rpow x (1 / 4 : ℝ) := by norm_num
    have hnum :
        Real.sqrt x + Real.rpow x (1 / 3 : ℝ) +
            Real.rpow x (1 / 4 : ℝ) =
          Real.sqrt x *
            (1 + Real.rpow x (-1 / 6 : ℝ) +
              Real.rpow x (-1 / 4 : ℝ)) := by
      rw [mul_add, mul_add, mul_one, hmul13, hmul14]
    have hrad : 2 * x + 1 = x * (2 + 1 / x) := by
      field_simp [hxne]
    have hden :
        Real.sqrt (2 * x + 1) =
          Real.sqrt x * Real.sqrt (2 + 1 / x) := by
      rw [hrad]
      exact Real.sqrt_mul hx0 _
    have hsqrtne : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
    have hnormpos : 0 < Real.sqrt (2 + 1 / x) := by positivity
    have hnormne : Real.sqrt (2 + 1 / x) ≠ 0 := ne_of_gt hnormpos
    unfold original normalized
    rw [hnum, hden]
    field_simp [hsqrtne, hnormne]
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

/-- Exercise 436, gap 2. -/
theorem gap2 : HasLimitAtPosInfinity normalized (1 / Real.sqrt 2) := by
  have hr6 :
      Filter.Tendsto (fun x : ℝ => Real.rpow x (-1 / 6 : ℝ))
        Filter.atTop (nhds 0) := by
    have h := tendsto_rpow_neg_atTop
      (show (0 : ℝ) < 1 / 6 by norm_num)
    change Filter.Tendsto
      (fun x : ℝ => Real.rpow x (-(1 / 6 : ℝ)))
      Filter.atTop (nhds 0) at h
    simpa only [show (-1 / 6 : ℝ) = -(1 / 6 : ℝ) by ring] using h
  have hr4 :
      Filter.Tendsto (fun x : ℝ => Real.rpow x (-1 / 4 : ℝ))
        Filter.atTop (nhds 0) := by
    have h := tendsto_rpow_neg_atTop
      (show (0 : ℝ) < 1 / 4 by norm_num)
    change Filter.Tendsto
      (fun x : ℝ => Real.rpow x (-(1 / 4 : ℝ)))
      Filter.atTop (nhds 0) at h
    simpa only [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring] using h
  have hinv :
      Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have htwo :
      Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) Filter.atTop (nhds 2) :=
    tendsto_const_nhds
  have hnum :
      Filter.Tendsto
        (fun x : ℝ =>
          1 + Real.rpow x (-1 / 6 : ℝ) +
            Real.rpow x (-1 / 4 : ℝ))
        Filter.atTop (nhds 1) := by
    simpa only [add_zero] using (hone.add hr6).add hr4
  have hdenArg :
      Filter.Tendsto (fun x : ℝ => 2 + 1 / x)
        Filter.atTop (nhds 2) := by
    simpa only [add_zero] using htwo.add hinv
  have hden :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (2 + 1 / x))
        Filter.atTop (nhds (Real.sqrt 2)) := by
    exact Real.continuous_sqrt.continuousAt.tendsto.comp hdenArg
  have hsqrt2ne : Real.sqrt 2 ≠ 0 := by positivity
  have hlim :
      Filter.Tendsto normalized Filter.atTop
        (nhds (1 / Real.sqrt 2)) := by
    unfold normalized
    exact hnum.div hden hsqrt2ne
  intro ε hε
  have hev :
      ∀ᶠ x : ℝ in Filter.atTop,
        dist (normalized x) (1 / Real.sqrt 2) < ε :=
    (Metric.tendsto_nhds.1 hlim) ε hε
  rcases (Filter.eventually_atTop.1 hev) with ⟨N, hN⟩
  refine ⟨max N 1, lt_of_lt_of_le zero_lt_one (le_max_right N 1), ?_⟩
  intro x hx
  have hxN : N ≤ x :=
    le_trans (le_max_left N 1) (le_of_lt hx)
  simpa [Real.dist_eq] using hN x hxN

/-- Exercise 436, gap 3. -/
theorem gap3 : HasLimitAtPosInfinity original (1 / Real.sqrt 2) := by
  exact gap1.mpr gap2

end

end ProofGap.Exercise436
