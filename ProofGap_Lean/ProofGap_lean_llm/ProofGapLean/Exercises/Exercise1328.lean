import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1328

noncomputable section
open Filter
open scoped Topology

def rightPunctured (x₀ : ℝ) := nhdsWithin x₀ (Set.Ioi x₀)
def original (a b x : ℝ) :=
  (Real.sqrt a * Real.arctan (Real.sqrt (x / a)) -
    Real.sqrt b * Real.arctan (Real.sqrt (x / b))) /
      (x * Real.sqrt x)
def simplified (a b x : ℝ) :=
  (a / (x + a) - b / (x + b)) / (3 * x)
def derivativeStage (a b x : ℝ) :=
  (-a / (x + a) ^ 2 + b / (x + b) ^ 2) / 3

private theorem limit_pair (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (original a b) (rightPunctured 0)
        (nhds ((a - b) / (3 * a * b))) ∧
      Tendsto (simplified a b) (rightPunctured 0)
        (nhds ((a - b) / (3 * a * b))) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have heq :
      simplified a b =ᶠ[rightPunctured 0]
        (fun x => (a - b) / (3 * (x + a) * (x + b))) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hxa : x + a ≠ 0 := ne_of_gt (add_pos hx ha)
    have hxb : x + b ≠ 0 := ne_of_gt (add_pos hx hb)
    unfold simplified
    field_simp [hx0, hxa, hxb]
    ring
  have hcont : ContinuousAt
      (fun x : ℝ => (a - b) / (3 * (x + a) * (x + b))) 0 := by
    have hd : ContinuousAt
        (fun x : ℝ => 3 * (x + a) * (x + b)) 0 :=
      (continuousAt_const.mul (continuousAt_id.add continuousAt_const)).mul
        (continuousAt_id.add continuousAt_const)
    exact continuousAt_const.div hd (by simp [ha0, hb0])
  have hval :
      (a - b) / (3 * (0 + a) * (0 + b)) =
        (a - b) / (3 * a * b) := by ring
  have hg : Tendsto
      (fun x : ℝ => (a - b) / (3 * (x + a) * (x + b)))
      (rightPunctured 0) (nhds ((a - b) / (3 * a * b))) := by
    rw [← hval]
    exact hcont.tendsto.mono_left
      (show rightPunctured 0 ≤ 𝓝 0 by
        unfold rightPunctured
        exact inf_le_left)
  have hsimp : Tendsto (simplified a b) (rightPunctured 0)
      (nhds ((a - b) / (3 * a * b))) :=
    hg.congr' heq.symm
  have hxa_tendsto : Tendsto (fun x : ℝ => x / a)
      (rightPunctured 0) (nhds 0) := by
    have hc : ContinuousAt (fun x : ℝ => x / a) 0 :=
      continuousAt_id.div_const a
    simpa using hc.tendsto.mono_left
      (show rightPunctured 0 ≤ 𝓝 0 by
        unfold rightPunctured
        exact inf_le_left)
  have hxb_tendsto : Tendsto (fun x : ℝ => x / b)
      (rightPunctured 0) (nhds 0) := by
    have hc : ContinuousAt (fun x : ℝ => x / b) 0 :=
      continuousAt_id.div_const b
    simpa using hc.tendsto.mono_left
      (show rightPunctured 0 ≤ 𝓝 0 by
        unfold rightPunctured
        exact inf_le_left)
  have hsa : Tendsto (fun x : ℝ => Real.sqrt (x / a))
      (rightPunctured 0) (nhds 0) := by
    simpa using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hxa_tendsto)
  have hsb : Tendsto (fun x : ℝ => Real.sqrt (x / b))
      (rightPunctured 0) (nhds 0) := by
    simpa using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hxb_tendsto)
  have hta : Tendsto
      (fun x : ℝ => Real.arctan (Real.sqrt (x / a)))
      (rightPunctured 0) (nhds 0) := by
    simpa using
      (Real.continuous_arctan.continuousAt.tendsto.comp hsa)
  have htb : Tendsto
      (fun x : ℝ => Real.arctan (Real.sqrt (x / b)))
      (rightPunctured 0) (nhds 0) := by
    simpa using
      (Real.continuous_arctan.continuousAt.tendsto.comp hsb)
  have hnum0 : Tendsto
      (fun x : ℝ =>
        Real.sqrt a * Real.arctan (Real.sqrt (x / a)) -
          Real.sqrt b * Real.arctan (Real.sqrt (x / b)))
      (rightPunctured 0) (nhds 0) := by
    have hca : Tendsto (fun _ : ℝ => Real.sqrt a)
        (rightPunctured 0) (nhds (Real.sqrt a)) := tendsto_const_nhds
    have hcb : Tendsto (fun _ : ℝ => Real.sqrt b)
        (rightPunctured 0) (nhds (Real.sqrt b)) := tendsto_const_nhds
    simpa using (hca.mul hta).sub (hcb.mul htb)
  have hden0 : Tendsto (fun x : ℝ => x * Real.sqrt x)
      (rightPunctured 0) (nhds 0) := by
    have hc : ContinuousAt (fun x : ℝ => x * Real.sqrt x) 0 :=
      continuousAt_id.mul Real.continuous_sqrt.continuousAt
    simpa using hc.tendsto.mono_left
      (show rightPunctured 0 ≤ 𝓝 0 by
        unfold rightPunctured
        exact inf_le_left)
  let dn : ℝ → ℝ := fun x =>
    (a / (x + a) - b / (x + b)) / (2 * Real.sqrt x)
  let dd : ℝ → ℝ := fun x => 3 * Real.sqrt x / 2
  have hnum_deriv : ∀ x, 0 < x → HasDerivAt
      (fun x : ℝ =>
        Real.sqrt a * Real.arctan (Real.sqrt (x / a)) -
          Real.sqrt b * Real.arctan (Real.sqrt (x / b))) (dn x) x := by
    intro x hx
    have hxa0 : x / a ≠ 0 := div_ne_zero (ne_of_gt hx) ha0
    have hxb0 : x / b ≠ 0 := div_ne_zero (ne_of_gt hx) hb0
    have hsa0 : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ha)
    have hsb0 : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hb)
    have hsx0 : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
    have hxa : x + a ≠ 0 := ne_of_gt (add_pos hx ha)
    have hxb : x + b ≠ 0 := ne_of_gt (add_pos hx hb)
    have hda :=
      ((Real.hasDerivAt_arctan _).comp x
        ((Real.hasDerivAt_sqrt hxa0).comp x
          ((hasDerivAt_id x).div_const a))).const_mul (Real.sqrt a)
    have hdb :=
      ((Real.hasDerivAt_arctan _).comp x
        ((Real.hasDerivAt_sqrt hxb0).comp x
          ((hasDerivAt_id x).div_const b))).const_mul (Real.sqrt b)
    have hsa2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
    have hsb2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
    have hsx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
    have hsa4 : Real.sqrt a ^ 4 = a ^ 2 := by
      calc
        Real.sqrt a ^ 4 = (Real.sqrt a ^ 2) ^ 2 := by ring
        _ = a ^ 2 := by rw [hsa2]
    have hsb4 : Real.sqrt b ^ 4 = b ^ 2 := by
      calc
        Real.sqrt b ^ 4 = (Real.sqrt b ^ 2) ^ 2 := by ring
        _ = b ^ 2 := by rw [hsb2]
    have hca :
        Real.sqrt a *
            (1 / (1 + (Real.sqrt (x / a)) ^ 2) *
              (1 / (2 * Real.sqrt (x / a)) * (1 / a))) =
          (a / (x + a)) / (2 * Real.sqrt x) := by
      rw [Real.sqrt_div hx.le]
      field_simp [ha0, hsa0, hsx0, hxa]
      rw [hsa4, hsa2, hsx2]
      ring
    have hcb :
        Real.sqrt b *
            (1 / (1 + (Real.sqrt (x / b)) ^ 2) *
              (1 / (2 * Real.sqrt (x / b)) * (1 / b))) =
          (b / (x + b)) / (2 * Real.sqrt x) := by
      rw [Real.sqrt_div hx.le]
      field_simp [hb0, hsb0, hsx0, hxb]
      rw [hsb4, hsb2, hsx2]
      ring
    have hd := hda.sub hdb
    simp only [Function.comp_apply, id_eq] at hd
    rw [hca, hcb] at hd
    convert hd using 1
    dsimp [dn]
    ring
  have hden_deriv : ∀ x, 0 < x →
      HasDerivAt (fun x : ℝ => x * Real.sqrt x) (dd x) x := by
    intro x hx
    have hsx0 : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
    have hd := (hasDerivAt_id x).mul (Real.hasDerivAt_sqrt (ne_of_gt hx))
    simp only [id_eq] at hd
    convert hd using 1
    dsimp [dd]
    field_simp [hsx0]
    rw [Real.sq_sqrt hx.le]
    ring
  have hratio_eq :
      (fun x => dn x / dd x) =ᶠ[rightPunctured 0] simplified a b := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hsx0 : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
    dsimp [dn, dd]
    unfold simplified
    field_simp [hx0, hsx0]
    rw [Real.sq_sqrt hx.le]
    ring
  have hratio : Tendsto (fun x => dn x / dd x) (rightPunctured 0)
      (nhds ((a - b) / (3 * a * b))) :=
    hsimp.congr' hratio_eq.symm
  have hdd_ne : ∀ x, 0 < x → dd x ≠ 0 := by
    intro x hx
    dsimp [dd]
    exact div_ne_zero
      (mul_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.2 hx)))
      (by norm_num)
  have horig : Tendsto
      (fun x : ℝ =>
        (Real.sqrt a * Real.arctan (Real.sqrt (x / a)) -
          Real.sqrt b * Real.arctan (Real.sqrt (x / b))) /
            (x * Real.sqrt x))
      (rightPunctured 0) (nhds ((a - b) / (3 * a * b))) := by
    have hnum_deriv_ev : ∀ᶠ x in rightPunctured 0, HasDerivAt
        (fun x : ℝ =>
          Real.sqrt a * Real.arctan (Real.sqrt (x / a)) -
            Real.sqrt b * Real.arctan (Real.sqrt (x / b))) (dn x) x := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hnum_deriv x hx
    have hden_deriv_ev : ∀ᶠ x in rightPunctured 0,
        HasDerivAt (fun x : ℝ => x * Real.sqrt x) (dd x) x := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hden_deriv x hx
    have hdd_ne_ev : ∀ᶠ x in rightPunctured 0, dd x ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hdd_ne x hx
    apply HasDerivAt.lhopital_zero_nhdsGT
      (f' := dn) (g' := dd)
      (hff' := hnum_deriv_ev) (hgg' := hden_deriv_ev)
      (hg' := hdd_ne_ev)
    all_goals first
      | exact hnum0
      | exact hden0
      | exact hratio
  constructor
  · simpa [original] using horig
  · exact hsimp

theorem gap1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (original a b) (rightPunctured 0)
      (nhds ((a - b) / (3 * a * b))) := by
  exact (limit_pair a b ha hb).1
theorem gap2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (simplified a b) (rightPunctured 0)
      (nhds ((a - b) / (3 * a * b))) := by
  exact (limit_pair a b ha hb).2
theorem gap3 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (derivativeStage a b) (rightPunctured 0)
      (nhds ((a - b) / (3 * a * b))) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hca : ContinuousAt (fun x : ℝ => (x + a) ^ 2) 0 :=
    (continuousAt_id.add continuousAt_const).pow 2
  have hcb : ContinuousAt (fun x : ℝ => (x + b) ^ 2) 0 :=
    (continuousAt_id.add continuousAt_const).pow 2
  have hc : ContinuousAt (derivativeStage a b) 0 := by
    unfold derivativeStage
    apply ContinuousAt.div_const
    apply ContinuousAt.add
    · exact continuousAt_const.div hca (by simp [ha0])
    · exact continuousAt_const.div hcb (by simp [hb0])
  have hval : derivativeStage a b 0 = (a - b) / (3 * a * b) := by
    unfold derivativeStage
    field_simp [ha0, hb0]
    ring
  rw [← hval]
  exact hc.tendsto.mono_left
    (show rightPunctured 0 ≤ 𝓝 0 by
      unfold rightPunctured
      exact inf_le_left)
theorem gap4 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (derivativeStage a b) (rightPunctured 0)
      (nhds ((a - b) / (3 * a * b))) := by
  exact gap3 a b ha hb
theorem gap5 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (original a b) (rightPunctured 0)
      (nhds ((a - b) / (3 * a * b))) := by
  exact gap1 a b ha hb

end
end ProofGap.Exercise1328
