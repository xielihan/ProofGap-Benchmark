import ProofGapLean.Prelude.Analysis
import Mathlib.Order.Filter.Prod
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3186

noncomputable section

open Filter
open scoped Topology

def atTop₂ : Filter (ℝ × ℝ) :=
  (atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)

def target (p : ℝ × ℝ) : ℝ :=
  (p.1 ^ 2 + p.2 ^ 2) / (p.1 ^ 4 + p.2 ^ 4)

def upperBound (p : ℝ × ℝ) : ℝ :=
  1 / 2 * (1 / p.1 ^ 2 + 1 / p.2 ^ 2)

/-- Exercise 3186, gap 1; exclude the simultaneous zero. -/
private theorem tendsto_coords_atTop₂ :
    Tendsto (fun p : ℝ × ℝ => p.1) atTop₂ atTop ∧
      Tendsto (fun p : ℝ × ℝ => p.2) atTop₂ atTop := by
  constructor
  · rw [tendsto_def]
    intro s hs
    rw [atTop₂]
    filter_upwards [Filter.prod_mem_prod hs
      (univ_mem : Set.univ ∈ (atTop : Filter ℝ))] with p hp
    exact hp.1
  · rw [tendsto_def]
    intro s hs
    rw [atTop₂]
    filter_upwards [Filter.prod_mem_prod
      (univ_mem : Set.univ ∈ (atTop : Filter ℝ)) hs] with p hp
    exact hp.2

theorem gap1 :
    ∀ x y : ℝ, (x, y) ≠ (0, 0) →
      0 ≤ (x ^ 2 + y ^ 2) / (x ^ 4 + y ^ 4) := by
  intro x y _
  exact div_nonneg (by positivity) (by positivity)

/-- Exercise 3186, gap 2; the comparison denominator needs `xy≠0`. -/
theorem gap2 :
    ∀ x y : ℝ, x ≠ 0 → y ≠ 0 →
      (x ^ 2 + y ^ 2) / (x ^ 4 + y ^ 4) ≤
        (x ^ 2 + y ^ 2) / (2 * x ^ 2 * y ^ 2) := by
  intro x y hx hy
  have hnum : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  have hden_left : 0 < x ^ 4 + y ^ 4 := by positivity
  have hden_right : 0 < 2 * x ^ 2 * y ^ 2 := by positivity
  have hden : 2 * x ^ 2 * y ^ 2 ≤ x ^ 4 + y ^ 4 := by
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
  apply (div_le_div_iff₀ hden_left hden_right).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (mul_le_mul_of_nonneg_left hden hnum)

/-- Exercise 3186, gap 3; algebra with nonzero coordinates. -/
theorem gap3 :
    ∀ x y : ℝ, x ≠ 0 → y ≠ 0 →
      (x ^ 2 + y ^ 2) / (2 * x ^ 2 * y ^ 2) =
        1 / 2 * (1 / x ^ 2 + 1 / y ^ 2) := by
  intro x y hx hy
  field_simp [hx, hy] <;> ring

/-- Exercise 3186, gap 4; reciprocal squares are defined off zero. -/
theorem gap4 :
    ∀ x y : ℝ, x ≠ 0 → y ≠ 0 →
      0 ≤ 1 / 2 * (1 / x ^ 2 + 1 / y ^ 2) := by
  intro x y _ _
  positivity

/-- Exercise 3186, gap 5; product-filter upper-bound limit. -/
theorem gap5 :
    Tendsto upperBound atTop₂ (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  have hsquare : Tendsto (fun x : ℝ => 1 / x ^ 2) atTop (𝓝 0) := by
    simpa [one_div, pow_two] using hinv.mul hinv
  have hx := hsquare.comp tendsto_coords_atTop₂.1
  have hy := hsquare.comp tendsto_coords_atTop₂.2
  have hhalf :
      Tendsto (fun _ : ℝ × ℝ => (1 / 2 : ℝ)) atTop₂ (𝓝 (1 / 2)) :=
    tendsto_const_nhds
  change Tendsto
    (fun p : ℝ × ℝ => 1 / 2 * (1 / p.1 ^ 2 + 1 / p.2 ^ 2))
    atTop₂ (𝓝 0)
  simpa only [one_div, pow_two, inv_zero, add_zero, mul_zero] using
    hhalf.mul (hx.add hy)

/-- Exercise 3186, gap 6; squeeze at `(∞,∞)`. -/
theorem gap6 :
    Tendsto target atTop₂ (𝓝 0) := by
  have hx : ∀ᶠ p : ℝ × ℝ in atTop₂, 0 < p.1 :=
    tendsto_coords_atTop₂.1.eventually (eventually_gt_atTop 0)
  have hy : ∀ᶠ p : ℝ × ℝ in atTop₂, 0 < p.2 :=
    tendsto_coords_atTop₂.2.eventually (eventually_gt_atTop 0)
  refine squeeze_zero' ?_ ?_ gap5
  · filter_upwards [hx, hy] with p hpx hpy
    have hpne : (p.1, p.2) ≠ ((0, 0) : ℝ × ℝ) := by
      intro h
      exact (ne_of_gt hpx) (congrArg Prod.fst h)
    simpa only [target] using (gap1 p.1 p.2 hpne)
  · filter_upwards [hx, hy] with p hpx hpy
    have hpx0 : p.1 ≠ 0 := ne_of_gt hpx
    have hpy0 : p.2 ≠ 0 := ne_of_gt hpy
    have hupper : target p ≤ upperBound p := by
      calc
        target p = (p.1 ^ 2 + p.2 ^ 2) / (p.1 ^ 4 + p.2 ^ 4) := rfl
        _ ≤ (p.1 ^ 2 + p.2 ^ 2) / (2 * p.1 ^ 2 * p.2 ^ 2) :=
          gap2 p.1 p.2 hpx0 hpy0
        _ = upperBound p := by
          simpa only [upperBound] using (gap3 p.1 p.2 hpx0 hpy0)
    exact hupper

end

end ProofGap.Exercise3186
