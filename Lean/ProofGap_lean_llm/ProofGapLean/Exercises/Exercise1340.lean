import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1340

noncomputable section

def HasLeftLimit (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 1 (Set.Iio 1)) (nhds L)

def f₀ (x : ℝ) : ℝ := Real.log x * Real.log (1 - x)
def f₁ (x : ℝ) : ℝ := Real.log (1 - x) / (1 / Real.log x)
def f₂ (x : ℝ) : ℝ :=
  (-1 / (1 - x)) / (-1 / (x * Real.log x ^ 2))
def f₃ (x : ℝ) : ℝ := x * Real.log x ^ 2 / (1 - x)
def f₄ (x : ℝ) : ℝ := (Real.log x ^ 2 + 2 * Real.log x) / (-1)

private theorem exercise1340_limits :
    HasLeftLimit f₀ 0 ∧ HasLeftLimit f₁ 0 ∧ HasLeftLimit f₂ 0 ∧
      HasLeftLimit f₃ 0 ∧ HasLeftLimit f₄ 0 := by
  let l := nhdsWithin (1 : ℝ) (Set.Iio 1)
  have hl : l = nhdsWithin (1 : ℝ) (Set.Iio 1) := rfl
  have hsubset : Set.Iio (1 : ℝ) ⊆ ({1} : Set ℝ)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_lt hx
  have hlogderiv : HasDerivAt Real.log 1 1 := by
    simpa using Real.hasDerivAt_log (show (1 : ℝ) ≠ 0 by norm_num)
  have hslope :
      Filter.Tendsto (slope Real.log 1)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 1) :=
    hlogderiv.tendsto_slope
  have hslope_left :
      Filter.Tendsto (slope Real.log 1) l (nhds 1) :=
    hslope.mono_left (nhdsWithin_mono 1 hsubset)
  have heqratio :
      (fun x : ℝ => -(slope Real.log 1 x)) =ᶠ[l]
        (fun x : ℝ => Real.log x / (1 - x)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxlt : x < 1 := hx
    have hxne : x - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hxlt)
    have hsubne : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hxlt)
    simp only [slope, Real.log_one, vsub_eq_sub, sub_zero, smul_eq_mul]
    field_simp [hxne, hsubne]
    ring_nf
  have hratio :
      Filter.Tendsto (fun x : ℝ => Real.log x / (1 - x)) l (nhds (-1)) := by
    exact hslope_left.neg.congr' heqratio
  have hxlim : Filter.Tendsto (fun x : ℝ => x) l (nhds 1) := by
    exact continuousAt_id.tendsto.mono_left inf_le_left
  have hlog : Filter.Tendsto Real.log l (nhds 0) := by
    simpa using
      ((Real.continuousAt_log (show (1 : ℝ) ≠ 0 by norm_num)).tendsto.mono_left
        inf_le_left)
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) l (nhds 1) :=
    tendsto_const_nhds
  have hsub0 :
      Filter.Tendsto (fun x : ℝ => 1 - x) l (nhds 0) := by
    simpa using hone.sub hxlim
  have hpos : ∀ᶠ x : ℝ in l, 0 < x := by
    exact
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        inf_le_left
  have hsqrt :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 - x)) l (nhds 0) := by
    have hsqrt' := Real.continuous_sqrt.continuousAt.tendsto.comp hsub0
    simpa using hsqrt'
  have htwo :
      Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) l (nhds 2) :=
    tendsto_const_nhds
  have htwosqrt :
      Filter.Tendsto (fun x : ℝ => 2 * Real.sqrt (1 - x)) l (nhds 0) := by
    simpa using htwo.mul hsqrt
  have hmullog :
      Filter.Tendsto
        (fun x : ℝ => (1 - x) * Real.log (1 - x)) l (nhds 0) := by
    rw [Metric.tendsto_nhds] at htwosqrt ⊢
    intro ε hε
    filter_upwards [htwosqrt ε hε, self_mem_nhdsWithin, hpos] with x heps hx hxp
    have hxlt : x < 1 := hx
    let t : ℝ := 1 - x
    let s : ℝ := Real.sqrt t
    have htpos : 0 < t := by
      dsimp [t]
      exact sub_pos.mpr hxlt
    have htlt : t < 1 := by
      dsimp [t]
      linarith
    have hspos : 0 < s := by
      dsimp [s]
      exact Real.sqrt_pos.2 htpos
    have hsne : s ≠ 0 := ne_of_gt hspos
    have hsq : s * s = t := by
      dsimp [s]
      exact Real.mul_self_sqrt htpos.le
    have hlogneg : Real.log t < 0 := Real.log_neg htpos htlt
    have hlogmul : Real.log t = Real.log s + Real.log s := by
      rw [← hsq, Real.log_mul hsne hsne]
    have hbraw : -Real.log s ≤ 1 / s - 1 := by
      calc
        -Real.log s = Real.log (1 / s) := by
          rw [one_div, Real.log_inv]
        _ ≤ 1 / s - 1 :=
          Real.log_le_sub_one_of_pos (one_div_pos.mpr hspos)
    have hb : s * (-Real.log s) ≤ 1 - s := by
      calc
        s * (-Real.log s) ≤ s * (1 / s - 1) :=
          mul_le_mul_of_nonneg_left hbraw hspos.le
        _ = 1 - s := by
          field_simp [hsne]
    have hmain : -(t * Real.log t) ≤ 2 * s := by
      calc
        -(t * Real.log t) = 2 * s * (s * (-Real.log s)) := by
          rw [hlogmul, ← hsq]
          ring
        _ ≤ 2 * s * (1 - s) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
        _ ≤ 2 * s := by
          nlinarith [sq_nonneg s]
    have hbound : |t * Real.log t| ≤ 2 * s := by
      rw [abs_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos htpos.le (le_of_lt hlogneg))]
      exact hmain
    have heps' : 2 * s < ε := by
      dsimp [s, t]
      simpa [Real.dist_eq, abs_of_nonneg (Real.sqrt_nonneg _)] using heps
    simpa [Real.dist_eq, t] using lt_of_le_of_lt hbound heps'
  have hprod0 :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.log x / (1 - x)) * ((1 - x) * Real.log (1 - x)))
        l (nhds 0) := by
    simpa using hratio.mul hmullog
  have heq0 :
      (fun x : ℝ =>
        (Real.log x / (1 - x)) * ((1 - x) * Real.log (1 - x))) =ᶠ[l]
        f₀ := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxlt : x < 1 := hx
    have hne : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hxlt)
    dsimp [f₀]
    field_simp [hne] <;> ring
  have hf0 : HasLeftLimit f₀ 0 := by
    unfold HasLeftLimit
    rw [← hl]
    exact hprod0.congr' heq0
  have heq01 : f₀ =ᶠ[l] f₁ := by
    filter_upwards [self_mem_nhdsWithin, hpos] with x hx hxp
    have hxlt : x < 1 := hx
    have hlogneg : Real.log x < 0 := Real.log_neg hxp hxlt
    have hlogne : Real.log x ≠ 0 := ne_of_lt hlogneg
    dsimp [f₀, f₁]
    field_simp [hlogne] <;> ring
  have hf1 : HasLeftLimit f₁ 0 := by
    unfold HasLeftLimit at hf0 ⊢
    rw [← hl] at hf0 ⊢
    exact hf0.congr' heq01
  have hprod3 :
      Filter.Tendsto
        (fun x : ℝ => x * ((Real.log x / (1 - x)) * Real.log x))
        l (nhds 0) := by
    simpa using hxlim.mul (hratio.mul hlog)
  have heq3 :
      (fun x : ℝ => x * ((Real.log x / (1 - x)) * Real.log x)) =ᶠ[l]
        f₃ := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxlt : x < 1 := hx
    have hne : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hxlt)
    dsimp [f₃]
    field_simp [hne] <;> ring
  have hf3 : HasLeftLimit f₃ 0 := by
    unfold HasLeftLimit
    rw [← hl]
    exact hprod3.congr' heq3
  have heq23 : f₂ =ᶠ[l] f₃ := by
    filter_upwards [self_mem_nhdsWithin, hpos] with x hx hxp
    have hxlt : x < 1 := hx
    have hsubne : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hxlt)
    have hlogneg : Real.log x < 0 := Real.log_neg hxp hxlt
    have hlogne : Real.log x ≠ 0 := ne_of_lt hlogneg
    have hxne : x ≠ 0 := ne_of_gt hxp
    dsimp [f₂, f₃]
    field_simp [hsubne, hlogne, hxne] <;> ring
  have hf2 : HasLeftLimit f₂ 0 := by
    unfold HasLeftLimit at hf3 ⊢
    rw [← hl] at hf3 ⊢
    exact hf3.congr' heq23.symm
  have hsum :
      Filter.Tendsto
        (fun x : ℝ => Real.log x ^ 2 + 2 * Real.log x) l (nhds 0) := by
    simpa using (hlog.pow 2).add (htwo.mul hlog)
  have hf4 : HasLeftLimit f₄ 0 := by
    unfold HasLeftLimit
    rw [← hl]
    have heq4 :
        (fun x : ℝ => -(Real.log x ^ 2 + 2 * Real.log x)) = f₄ := by
      funext x
      dsimp [f₄]
      ring
    rw [← heq4]
    simpa using hsum.neg
  exact ⟨hf0, hf1, hf2, hf3, hf4⟩

theorem gap1 : HasLeftLimit f₀ 0 ↔ HasLeftLimit f₁ 0 := by
  have h := exercise1340_limits
  exact iff_of_true h.1 h.2.1
theorem gap2 : HasLeftLimit f₁ 0 ↔ HasLeftLimit f₂ 0 := by
  have h := exercise1340_limits
  exact iff_of_true h.2.1 h.2.2.1
theorem gap3 : HasLeftLimit f₂ 0 ↔ HasLeftLimit f₃ 0 := by
  have h := exercise1340_limits
  exact iff_of_true h.2.2.1 h.2.2.2.1
theorem gap4 : HasLeftLimit f₃ 0 ↔ HasLeftLimit f₄ 0 := by
  have h := exercise1340_limits
  exact iff_of_true h.2.2.2.1 h.2.2.2.2
theorem gap5 : HasLeftLimit f₄ 0 := by
  exact exercise1340_limits.2.2.2.2
theorem gap6 : HasLeftLimit f₀ 0 := by
  exact exercise1340_limits.1

end

end ProofGap.Exercise1340
