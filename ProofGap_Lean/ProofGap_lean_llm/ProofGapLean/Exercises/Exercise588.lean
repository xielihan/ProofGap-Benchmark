import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise588

noncomputable section

def original (x : ℝ) : ℝ :=
  x * (Real.pi / 4 - Real.arctan (x / (x + 1)))
def transformed (x : ℝ) : ℝ := x * Real.arctan (1 / (2 * x + 1))
def normalized (x : ℝ) : ℝ :=
  (Real.arctan (1 / (2 * x + 1)) / (1 / (2 * x + 1))) *
    (x / (2 * x + 1))
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Exercise 588, gap 1. -/
theorem gap1 (L : ℝ) :
    HasLimitAtPosInfinity original L ↔ HasLimitAtPosInfinity transformed L := by
  unfold HasLimitAtPosInfinity
  have heq : original =ᶠ[Filter.atTop] transformed := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hx1pos : 0 < x + 1 := by linarith
    have hx2pos : 0 < 2 * x + 1 := by linarith
    have hx1 : x + 1 ≠ 0 := ne_of_gt hx1pos
    have hx2 : 2 * x + 1 ≠ 0 := ne_of_gt hx2pos
    have ha : x / (x + 1) < 1 := by
      exact (div_lt_one hx1pos).2 (by linarith)
    have hbpos : 0 < 1 / (2 * x + 1) := by
      exact div_pos (by norm_num) hx2pos
    have hb : 1 / (2 * x + 1) < 1 := by
      exact (div_lt_one hx2pos).2 (by linarith)
    have hmul :
        (x / (x + 1)) * (1 / (2 * x + 1)) < 1 := by
      calc
        (x / (x + 1)) * (1 / (2 * x + 1)) <
            1 * (1 / (2 * x + 1)) :=
          mul_lt_mul_of_pos_right ha hbpos
        _ < 1 := by simpa using hb
    have hsub :
        1 - (x / (x + 1)) * (1 / (2 * x + 1)) ≠ 0 :=
      ne_of_gt (sub_pos.mpr hmul)
    have hrat :
        ((x / (x + 1) + 1 / (2 * x + 1)) /
            (1 - (x / (x + 1)) * (1 / (2 * x + 1)))) = (1 : ℝ) := by
      apply (div_eq_iff hsub).2
      field_simp [hx1, hx2]
      ring
    have hadd :
        Real.arctan (x / (x + 1)) +
            Real.arctan (1 / (2 * x + 1)) =
          Real.arctan
            ((x / (x + 1) + 1 / (2 * x + 1)) /
              (1 - (x / (x + 1)) * (1 / (2 * x + 1)))) :=
      Real.arctan_add hmul
    rw [hrat, Real.arctan_one] at hadd
    have hdiff :
        Real.pi / 4 - Real.arctan (x / (x + 1)) =
          Real.arctan (1 / (2 * x + 1)) := by
      linarith
    simp only [original, transformed, hdiff]
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Exercise 588, gap 2. -/
theorem gap2 (L : ℝ) :
    HasLimitAtPosInfinity transformed L ↔ HasLimitAtPosInfinity normalized L := by
  unfold HasLimitAtPosInfinity
  have heq : transformed =ᶠ[Filter.atTop] normalized := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hd : 2 * x + 1 ≠ 0 := by linarith
    have hu : 1 / (2 * x + 1) ≠ 0 := one_div_ne_zero hd
    unfold transformed normalized
    field_simp [hd, hu]
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Exercise 588, gap 3. -/
theorem gap3 : HasLimitAtPosInfinity normalized (1 / 2) := by
  unfold HasLimitAtPosInfinity
  have hden :
      Filter.Tendsto (fun x : ℝ => 2 * x + 1)
        Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop ((b - 1) / 2)] with x hx
    linarith
  have hu0 :
      Filter.Tendsto (fun x : ℝ => 1 / (2 * x + 1))
        Filter.atTop (nhds 0) := by
    simpa [one_div] using
      ((tendsto_inv_atTop_zero :
          Filter.Tendsto (fun y : ℝ => y⁻¹) Filter.atTop (nhds 0)).comp hden)
  have hu :
      Filter.Tendsto (fun x : ℝ => 1 / (2 * x + 1))
        Filter.atTop (nhdsWithin 0 ({0}ᶜ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hu0, ?_⟩
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hd : 2 * x + 1 ≠ 0 := by linarith
    have hne : 1 / (2 * x + 1) ≠ 0 := one_div_ne_zero hd
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hne
  have hbase :
      Filter.Tendsto
        (fun u : ℝ => Real.arctan u / u)
        (nhdsWithin 0 ({0}ᶜ)) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_arctan 0).tendsto_slope_zero
  have hfirst :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.arctan (1 / (2 * x + 1)) / (1 / (2 * x + 1)))
        Filter.atTop (nhds 1) :=
    hbase.comp hu
  have hv :
      Filter.Tendsto (fun x : ℝ => x / (2 * x + 1))
        Filter.atTop (nhds (1 / 2 : ℝ)) := by
    have hone :
        Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
          Filter.atTop (nhds 1) :=
      tendsto_const_nhds
    have haux :
        Filter.Tendsto
          (fun x : ℝ => (1 - 1 / (2 * x + 1)) / 2)
          Filter.atTop (nhds (1 / 2 : ℝ)) := by
      simpa using ((hone.sub hu0).div_const (2 : ℝ))
    apply haux.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hd : 2 * x + 1 ≠ 0 := by linarith
    field_simp [hd] <;> ring
  have hprod :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.arctan (1 / (2 * x + 1)) / (1 / (2 * x + 1))) *
            (x / (2 * x + 1)))
        Filter.atTop (nhds (1 / 2 : ℝ)) := by
    simpa using hfirst.mul hv
  simpa only [normalized] using hprod

/-- Exercise 588, gap 4. -/
theorem gap4 : HasLimitAtPosInfinity original (1 / 2) := by
  exact (gap1 (1 / 2)).mpr ((gap2 (1 / 2)).mpr gap3)

end

end ProofGap.Exercise588
