import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise828_3

noncomputable section

def y (x : ℝ) : ℝ := 1 / x

def quotient (x Δx : ℝ) : ℝ := (y (x + Δx) - y x) / Δx

/-- Source: `proof_gap/exercise_828_3/1.txt`; define `Δy` as the actual function increment. -/
private theorem y_hasDerivAt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt y (-1 / x ^ 2) x := by
  have hy : y = fun z : ℝ => z⁻¹ := by
    funext z
    simp [y]
  rw [hy]
  simpa using (hasDerivAt_id x).inv hx

theorem gap1 (x Δx Δy : ℝ) (hΔy : Δy = y (x + Δx) - y x) :
    Δy / Δx = (1 / (x + Δx) - 1 / x) / Δx := by
  simpa [y] using congrArg (fun z : ℝ => z / Δx) hΔy

/-- Source: `proof_gap/exercise_828_3/2.txt`; add all omitted nonzero denominators. -/
theorem gap2 (x Δx : ℝ) (hx : x ≠ 0) (hΔx : Δx ≠ 0)
    (hsum : x + Δx ≠ 0) :
    (1 / (x + Δx) - 1 / x) / Δx = -1 / (x * (Δx + x)) := by
  have hsum' : Δx + x ≠ 0 := by
    simpa [add_comm] using hsum
  field_simp [hx, hΔx, hsum, hsum'] <;> ring

/-- Source: `proof_gap/exercise_828_3/3.txt`; define `Δy` and add denominator hypotheses. -/
theorem gap3 (x Δx Δy : ℝ) (hx : x ≠ 0) (hΔx : Δx ≠ 0)
    (hsum : x + Δx ≠ 0) (hΔy : Δy = y (x + Δx) - y x) :
    Δy / Δx = -1 / (x * (Δx + x)) := by
  calc
    Δy / Δx = (1 / (x + Δx) - 1 / x) / Δx :=
      gap1 x Δx Δy hΔy
    _ = -1 / (x * (Δx + x)) := gap2 x Δx hx hΔx hsum

/-- Source: `proof_gap/exercise_828_3/4.txt`; replace the undefined limit-value term by `Tendsto`. -/
theorem gap4 (x : ℝ) (hx : x ≠ 0) :
    Filter.Tendsto (quotient x) (nhdsWithin 0 {0}ᶜ) (nhds (deriv y x)) := by
  have ht : ContinuousAt (fun Δx : ℝ => x + Δx) 0 :=
    continuousAt_const.add continuousAt_id
  have hval : (fun Δx : ℝ => x + Δx) 0 ≠ 0 := by
    simpa using hx
  have hsum : ∀ᶠ Δx : ℝ in nhds 0, x + Δx ≠ 0 := by
    exact ht.eventually (eventually_ne_nhds hval)
  have hsum' : ∀ᶠ Δx : ℝ in nhdsWithin 0 {0}ᶜ, x + Δx ≠ 0 :=
    hsum.filter_mono inf_le_left
  have heq : Filter.EventuallyEq (nhdsWithin 0 {0}ᶜ) (quotient x)
      (fun Δx => -1 / (x * (Δx + x))) := by
    filter_upwards [self_mem_nhdsWithin, hsum'] with Δx hΔx hsumΔx
    have hΔx0 : Δx ≠ 0 := by
      simpa using hΔx
    simpa [quotient, y] using gap2 x Δx hx hΔx0 hsumΔx
  have hcont :
      ContinuousAt (fun Δx : ℝ => (-1 : ℝ) / (x * (Δx + x))) 0 := by
    exact continuousAt_const.div
      (continuousAt_const.mul (continuousAt_id.add continuousAt_const))
      (by simpa using mul_ne_zero hx hx)
  have hlim :
      Filter.Tendsto (fun Δx : ℝ => (-1 : ℝ) / (x * (Δx + x)))
        (nhds 0) (nhds (-1 / x ^ 2)) := by
    simpa only [ContinuousAt, zero_add, pow_two] using hcont
  rw [(y_hasDerivAt x hx).deriv]
  exact Filter.Tendsto.congr' heq.symm (hlim.mono_left inf_le_left)

/-- Source: `proof_gap/exercise_828_3/5.txt`; state equality of the two punctured-limit representatives. -/
theorem gap5 (x : ℝ) (hx : x ≠ 0) :
    Filter.EventuallyEq (nhdsWithin 0 {0}ᶜ) (quotient x)
      (fun Δx => -1 / (x * (Δx + x))) := by
  have ht : ContinuousAt (fun Δx : ℝ => x + Δx) 0 :=
    continuousAt_const.add continuousAt_id
  have hval : (fun Δx : ℝ => x + Δx) 0 ≠ 0 := by
    simpa using hx
  have hsum : ∀ᶠ Δx : ℝ in nhds 0, x + Δx ≠ 0 := by
    exact ht.eventually (eventually_ne_nhds hval)
  have hsum' : ∀ᶠ Δx : ℝ in nhdsWithin 0 {0}ᶜ, x + Δx ≠ 0 :=
    hsum.filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hsum'] with Δx hΔx hsumΔx
  have hΔx0 : Δx ≠ 0 := by
    simpa using hΔx
  simpa [quotient, y] using gap2 x Δx hx hΔx0 hsumΔx

/-- Source: `proof_gap/exercise_828_3/6.txt`; add `x≠0`. -/
theorem gap6 (x : ℝ) (hx : x ≠ 0) :
    Filter.Tendsto (fun Δx => -1 / (x * (Δx + x)))
      (nhds 0) (nhds (-1 / x ^ 2)) := by
  have hcont :
      ContinuousAt (fun Δx : ℝ => (-1 : ℝ) / (x * (Δx + x))) 0 := by
    exact continuousAt_const.div
      (continuousAt_const.mul (continuousAt_id.add continuousAt_const))
      (by simpa using mul_ne_zero hx hx)
  simpa only [ContinuousAt, zero_add, pow_two] using hcont

/-- Source: `proof_gap/exercise_828_3/7.txt`; add `x≠0`. -/
theorem gap7 (x : ℝ) (hx : x ≠ 0) : deriv y x = -1 / x ^ 2 := by
  exact (y_hasDerivAt x hx).deriv

end

end ProofGap.Exercise828_3
