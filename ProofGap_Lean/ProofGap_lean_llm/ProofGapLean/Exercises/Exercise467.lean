import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

namespace ProofGap.Exercise467

noncomputable section

def a (x : ℝ) : ℝ := Real.sqrt (1 + x ^ 2) + x
def b (x : ℝ) : ℝ := Real.sqrt (1 + x ^ 2) - x
def original (n : ℕ) (x : ℝ) : ℝ := ((a x) ^ n - (b x) ^ n) / x
def geometricFactor (n : ℕ) (x : ℝ) : ℝ :=
  (Finset.range n).sum (fun k => (a x) ^ (n - 1 - k) * (b x) ^ k)
def transformed (n : ℕ) (x : ℝ) : ℝ := 2 * geometricFactor n x
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 467, gap 1; expand the difference of `n`th powers. -/
theorem gap1 (n : ℕ) (hn : 0 < n) (L : ℝ) :
    HasLimitAt (original n) 0 L ↔ HasLimitAt (transformed n) 0 L := by
  unfold HasLimitAt
  apply Filter.tendsto_congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by
    simpa using hx
  have hab : a x - b x = 2 * x := by
    unfold a b
    ring
  have hsum :
      (Finset.range n).sum (fun k => (b x) ^ k * (a x) ^ (n - 1 - k)) =
        geometricFactor n x := by
    unfold geometricFactor
    apply Finset.sum_congr rfl
    intro k hk
    exact mul_comm _ _
  have hgeom := geom_sum₂_mul (b x) (a x) n
  have hfactor :
      (a x) ^ n - (b x) ^ n = (a x - b x) * geometricFactor n x := by
    calc
      (a x) ^ n - (b x) ^ n = -((b x) ^ n - (a x) ^ n) := by ring
      _ = -((Finset.range n).sum
          (fun k => (b x) ^ k * (a x) ^ (n - 1 - k)) * (b x - a x)) := by
            rw [hgeom]
      _ = (a x - b x) * geometricFactor n x := by rw [hsum]; ring
  simp only [original, transformed]
  rw [hfactor, hab]
  field_simp [hx0]

/-- Exercise 467, gap 2. -/
theorem gap2 (n : ℕ) (hn : 0 < n) :
    HasLimitAt (transformed n) 0 (2 * n) := by
  unfold HasLimitAt
  have hcont : ContinuousAt (transformed n) 0 := by
    unfold transformed geometricFactor a b
    fun_prop
  have hvalue : transformed n 0 = 2 * (n : ℝ) := by
    simp [transformed, geometricFactor, a, b]
  rw [← hvalue]
  exact hcont.tendsto.mono_left inf_le_left

end

end ProofGap.Exercise467
