import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise573

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.rpow (2 * Real.exp (x / (x + 1)) - 1) ((x ^ 2 + 1) / x)
def exponentialForm (x : ℝ) : ℝ :=
  let q := 2 * (Real.exp (x / (x + 1)) - 1)
  Real.rpow (Real.rpow (1 + q) (1 / q))
    ((2 * (x ^ 2 + 1) / (x + 1)) *
      ((Real.exp (x / (x + 1)) - 1) / (x / (x + 1))))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_573/1.txt`. -/
theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero exponentialForm L := by
  unfold HasLimitAtZero
  have hxlim :
      Tendsto (fun x : ℝ => x) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using
      (continuousAt_id.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left))
  have hnear :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        x ∈ Set.Ioo (-(1 : ℝ) / 3) (1 / 3) :=
    hxlim
      (Ioo_mem_nhds
        (by norm_num : -(1 : ℝ) / 3 < 0)
        (by norm_num : (0 : ℝ) < 1 / 3))
  have heq :
      original =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] exponentialForm := by
    filter_upwards [hnear, self_mem_nhdsWithin] with x hx hxmem
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxmem
    have hxp : 0 < x + 1 := by
      linarith [hx.1]
    have ht0 : x / (x + 1) ≠ 0 :=
      div_ne_zero hx0 (ne_of_gt hxp)
    have ht_lower : -(1 : ℝ) / 2 < x / (x + 1) := by
      apply (lt_div_iff₀ hxp).2
      linarith [hx.1]
    have hexp_lower :
        1 + x / (x + 1) < Real.exp (x / (x + 1)) := by
      simpa [add_comm] using Real.add_one_lt_exp ht0
    have hbase : 0 < 2 * Real.exp (x / (x + 1)) - 1 := by
      linarith
    have hexpne : Real.exp (x / (x + 1)) - 1 ≠ 0 := by
      apply sub_ne_zero.mpr
      intro h
      have hz : x / (x + 1) = 0 :=
        Real.exp_injective (by simpa using h)
      exact ht0 hz
    unfold original exponentialForm
    dsimp only
    have hbase_eq :
        1 + 2 * (Real.exp (x / (x + 1)) - 1) =
          2 * Real.exp (x / (x + 1)) - 1 := by
      ring
    rw [hbase_eq]
    have hexponents :
        (x ^ 2 + 1) / x =
          (1 / (2 * (Real.exp (x / (x + 1)) - 1))) *
            (2 * (x ^ 2 + 1) / (x + 1) *
              ((Real.exp (x / (x + 1)) - 1) / (x / (x + 1)))) := by
      field_simp [hx0, ne_of_gt hxp, hexpne] <;> ring
    have hrpow :
        Real.rpow (2 * Real.exp (x / (x + 1)) - 1)
            ((1 / (2 * (Real.exp (x / (x + 1)) - 1))) *
              (2 * (x ^ 2 + 1) / (x + 1) *
                ((Real.exp (x / (x + 1)) - 1) / (x / (x + 1))))) =
          Real.rpow
            (Real.rpow (2 * Real.exp (x / (x + 1)) - 1)
              (1 / (2 * (Real.exp (x / (x + 1)) - 1))))
            (2 * (x ^ 2 + 1) / (x + 1) *
              ((Real.exp (x / (x + 1)) - 1) / (x / (x + 1)))) := by
      exact Real.rpow_mul (le_of_lt hbase)
        (1 / (2 * (Real.exp (x / (x + 1)) - 1)))
        (2 * (x ^ 2 + 1) / (x + 1) *
          ((Real.exp (x / (x + 1)) - 1) / (x / (x + 1))))
    calc
      Real.rpow (2 * Real.exp (x / (x + 1)) - 1) ((x ^ 2 + 1) / x) =
          Real.rpow (2 * Real.exp (x / (x + 1)) - 1)
            ((1 / (2 * (Real.exp (x / (x + 1)) - 1))) *
              (2 * (x ^ 2 + 1) / (x + 1) *
                ((Real.exp (x / (x + 1)) - 1) / (x / (x + 1))))) :=
        congrArg
          (fun z : ℝ => Real.rpow (2 * Real.exp (x / (x + 1)) - 1) z)
          hexponents
      _ = _ := hrpow
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Source: `proof_gap/exercise_573/2.txt`. -/
theorem gap2 : HasLimitAtZero exponentialForm (Real.exp 2) := by
  unfold HasLimitAtZero
  let t : ℝ → ℝ := fun x => x / (x + 1)
  let q : ℝ → ℝ := fun x => 2 * (Real.exp (t x) - 1)
  let a : ℝ → ℝ := fun x => Real.rpow (1 + q x) (1 / q x)
  let b : ℝ → ℝ := fun x =>
    (2 * (x ^ 2 + 1) / (x + 1)) *
      ((Real.exp (t x) - 1) / t x)
  let l := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have hxlim : Tendsto (fun x : ℝ => x) l (nhds 0) := by
    simpa [l] using
      (continuousAt_id.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left))
  have hden : Tendsto (fun x : ℝ => x + 1) l (nhds 1) := by
    simpa using hxlim.add tendsto_const_nhds
  have ht : Tendsto t l (nhds 0) := by
    simpa [t] using hxlim.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hden_pos : ∀ᶠ x in l, 0 < x + 1 :=
    hden (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have ht_ne_event : ∀ᶠ x in l, t x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin, hden_pos] with x hx hxp
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    exact div_ne_zero hx0 (ne_of_gt hxp)
  have ht_within : Tendsto t l (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨ht, ?_⟩
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht_ne_event
  have hexpt : Tendsto (fun x => Real.exp (t x)) l (nhds 1) := by
    simpa using (Real.continuous_exp.tendsto 0).comp ht
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) l (nhds 1) :=
    tendsto_const_nhds
  have htwo : Tendsto (fun _ : ℝ => (2 : ℝ)) l (nhds 2) :=
    tendsto_const_nhds
  have hq : Tendsto q l (nhds 0) := by
    simpa [q] using htwo.mul (hexpt.sub hone)
  have hq_ne_event : ∀ᶠ x in l, q x ≠ 0 := by
    filter_upwards [ht_ne_event] with x htx
    have he : Real.exp (t x) - 1 ≠ 0 := by
      apply sub_ne_zero.mpr
      intro h
      have hz : t x = 0 := Real.exp_injective (by simpa using h)
      exact htx hz
    exact mul_ne_zero (by norm_num) he
  have hq_within : Tendsto q l (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hq, ?_⟩
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hq_ne_event
  have hlog_slope :
      Tendsto (fun z : ℝ => Real.log (1 + z) / z)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have hinner : HasDerivAt (fun z : ℝ => 1 + z) 1 0 := by
      simpa [add_comm] using
        (hasDerivAt_id (𝕜 := ℝ) 0).const_add (1 : ℝ)
    have houter : HasDerivAt Real.log 1 (1 + 0) := by
      simpa using
        Real.hasDerivAt_log (show (1 + 0 : ℝ) ≠ 0 by norm_num)
    have hd : HasDerivAt (fun z : ℝ => Real.log (1 + z)) 1 0 := by
      simpa [Function.comp_def] using houter.comp 0 hinner
    simpa [slope, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero
  have hexp_slope :
      Tendsto (fun z : ℝ => (Real.exp z - 1) / z)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [slope, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_exp 0).tendsto_slope_zero
  have hlogq :
      Tendsto (fun x => Real.log (1 + q x) / q x) l (nhds 1) :=
    hlog_slope.comp hq_within
  have hbase_pos : ∀ᶠ x in l, 0 < 1 + q x := by
    have hq_lower : ∀ᶠ x in l, -(1 : ℝ) < q x :=
      hq (Ioi_mem_nhds (by norm_num : -(1 : ℝ) < 0))
    filter_upwards [hq_lower] with x hx
    linarith
  have ha_eq :
      a =ᶠ[l] fun x => Real.exp (Real.log (1 + q x) / q x) := by
    filter_upwards [hbase_pos] with x hx
    have hrpow :
        Real.rpow (1 + q x) (1 / q x) =
          Real.exp (Real.log (1 + q x) * (1 / q x)) := by
      exact Real.rpow_def_of_pos hx (1 / q x)
    simpa only [a, div_eq_mul_inv, one_mul] using hrpow
  have ha_pos : ∀ᶠ x in l, 0 < a x := by
    filter_upwards [hbase_pos] with x hx
    exact Real.rpow_pos_of_pos hx _
  have hsq : Tendsto (fun x : ℝ => x ^ 2 + 1) l (nhds 1) := by
    simpa using (hxlim.pow 2).add tendsto_const_nhds
  have htwice :
      Tendsto (fun x : ℝ => 2 * (x ^ 2 + 1)) l (nhds 2) := by
    simpa using htwo.mul hsq
  have hfirst :
      Tendsto (fun x : ℝ => 2 * (x ^ 2 + 1) / (x + 1)) l (nhds 2) := by
    simpa using htwice.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hratio :
      Tendsto (fun x => (Real.exp (t x) - 1) / t x) l (nhds 1) :=
    hexp_slope.comp ht_within
  have hb : Tendsto b l (nhds 2) := by
    simpa [b] using hfirst.mul hratio
  have hloga_eq :
      (fun x => Real.log (a x)) =ᶠ[l]
        fun x => Real.log (1 + q x) / q x := by
    filter_upwards [ha_eq] with x hx
    calc
      Real.log (a x) =
          Real.log (Real.exp (Real.log (1 + q x) / q x)) :=
        congrArg Real.log hx
      _ = Real.log (1 + q x) / q x := Real.log_exp _
  have hloga : Tendsto (fun x => Real.log (a x)) l (nhds 1) :=
    hlogq.congr' hloga_eq.symm
  have hproduct :
      Tendsto (fun x => Real.log (a x) * b x) l (nhds 2) := by
    simpa using hloga.mul hb
  have hrepr :
      Tendsto (fun x => Real.exp (Real.log (a x) * b x)) l
        (nhds (Real.exp 2)) :=
    (Real.continuous_exp.tendsto 2).comp hproduct
  have hout_eq :
      exponentialForm =ᶠ[l]
        fun x => Real.exp (Real.log (a x) * b x) := by
    filter_upwards [ha_pos] with x hx
    change Real.rpow (a x) (b x) =
      Real.exp (Real.log (a x) * b x)
    exact Real.rpow_def_of_pos hx (b x)
  exact hrepr.congr' hout_eq.symm

/-- Source: `proof_gap/exercise_573/3.txt`. -/
theorem gap3 : HasLimitAtZero original (Real.exp 2) := by
  exact (gap1 (Real.exp 2)).2 gap2

end

end ProofGap.Exercise573
