import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise828_2

noncomputable section

def cube (x : ℝ) : ℝ := x ^ 3
def increment (x Δx : ℝ) : ℝ := cube (x + Δx) - cube x
def quotient (x Δx : ℝ) : ℝ := increment x Δx / Δx

/-- Exercise 828_2, gap 1; replace the false universal
quantifier over `Δy` by its increment definition and add `Δx≠0`. -/
private theorem hasDerivAt_cube (x : ℝ) : HasDerivAt cube (3 * x ^ 2) x := by
  change HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x
  have h := (hasDerivAt_id x).mul ((hasDerivAt_id x).mul (hasDerivAt_id x))
  convert h using 1
  · funext y
    simp [pow_succ, mul_assoc]
  · simp <;> ring

theorem gap1 (Δy Δx x : ℝ) (hΔy : Δy = increment x Δx)
    (hΔx : Δx ≠ 0) :
    Δy / Δx = ((x + Δx) ^ 3 - x ^ 3) / Δx := by
  simpa [hΔy, increment, cube]

/-- Exercise 828_2, gap 2; add `Δx≠0`. -/
theorem gap2 (x Δx : ℝ) (hΔx : Δx ≠ 0) :
    ((x + Δx) ^ 3 - x ^ 3) / Δx =
      3 * x ^ 2 + 3 * x * Δx + Δx ^ 2 := by
  field_simp [hΔx] <;> ring

/-- Exercise 828_2, gap 3; bind `Δy` and add `Δx≠0`. -/
theorem gap3 (Δy Δx x : ℝ) (hΔy : Δy = increment x Δx)
    (hΔx : Δx ≠ 0) :
    Δy / Δx = 3 * x ^ 2 + 3 * x * Δx + Δx ^ 2 := by
  calc
    Δy / Δx = ((x + Δx) ^ 3 - x ^ 3) / Δx := gap1 Δy Δx x hΔy hΔx
    _ = 3 * x ^ 2 + 3 * x * Δx + Δx ^ 2 := gap2 x Δx hΔx

/-- Exercise 828_2, gap 4; replace the unspecified `lim`
operator by the difference-quotient `Tendsto` statement. -/
theorem gap4 (x : ℝ) :
    Filter.Tendsto (quotient x) (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (deriv cube x)) := by
  rw [(hasDerivAt_cube x).deriv]
  have hid :
      Filter.Tendsto (fun Δx : ℝ => Δx)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    exact ContinuousAt.continuousWithinAt continuousAt_id
  have hpoly :
      Filter.Tendsto
        (fun Δx : ℝ => 3 * x ^ 2 + 3 * x * Δx + Δx ^ 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (3 * x ^ 2)) := by
    simpa using
      ((tendsto_const_nhds.add (tendsto_const_nhds.mul hid)).add (hid.pow 2))
  have heq :
      quotient x =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
        (fun Δx => 3 * x ^ 2 + 3 * x * Δx + Δx ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with Δx hΔx
    have hne : Δx ≠ 0 := by
      simpa using hΔx
    simpa [quotient, increment, cube] using gap2 x Δx hne
  change Filter.map (quotient x) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) ≤
    nhds (3 * x ^ 2)
  rw [Filter.map_congr heq]
  exact hpoly

/-- Exercise 828_2, gap 5; state equality of the two
punctured-limit formulations. -/
theorem gap5 (x L : ℝ) :
    Filter.Tendsto (quotient x) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L) ↔
      Filter.Tendsto (fun Δx => 3 * x ^ 2 + 3 * x * Δx + Δx ^ 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L) := by
  have heq :
      quotient x =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
        (fun Δx => 3 * x ^ 2 + 3 * x * Δx + Δx ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with Δx hΔx
    have hne : Δx ≠ 0 := by
      simpa using hΔx
    simpa [quotient, increment, cube] using gap2 x Δx hne
  change
    Filter.map (quotient x) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) ≤ nhds L ↔
      Filter.map (fun Δx => 3 * x ^ 2 + 3 * x * Δx + Δx ^ 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) ≤ nhds L
  rw [Filter.map_congr heq]

/-- Exercise 828_2, gap 6. -/
theorem gap6 (x : ℝ) :
    Filter.Tendsto (fun Δx => 3 * x ^ 2 + 3 * x * Δx + Δx ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (3 * x ^ 2)) := by
  have hid :
      Filter.Tendsto (fun Δx : ℝ => Δx)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    exact ContinuousAt.continuousWithinAt continuousAt_id
  simpa using
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul hid)).add (hid.pow 2))

/-- Exercise 828_2, gap 7. -/
theorem gap7 (x : ℝ) : HasDerivAt cube (3 * x ^ 2) x := by
  exact hasDerivAt_cube x

end

end ProofGap.Exercise828_2
