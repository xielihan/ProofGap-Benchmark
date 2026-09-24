import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise531

noncomputable section

def original (a x : ℝ) : ℝ := (Real.log x - Real.log a) / (x - a)
def quotientLog (a x : ℝ) : ℝ := Real.log (x / a) / (x - a)
def rewritten (a x : ℝ) : ℝ :=
  Real.log (Real.rpow (1 + 1 / (a / (x - a)))
    ((a / (x - a)) * (1 / a)))
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 531, gap 1. -/
private theorem originalLimitAt (a : ℝ) (ha : 0 < a) :
    HasLimitAt (original a) a (1 / a) := by
  unfold HasLimitAt
  have hslope := (Real.hasDerivAt_log ha.ne').tendsto_slope
  have hslope' :
      Filter.Tendsto (slope Real.log a) (nhdsWithin a ({a} : Set ℝ)ᶜ)
        (nhds (1 / a)) := by
    simpa only [one_div] using hslope
  refine hslope'.congr' (Filter.Eventually.of_forall fun x => ?_)
  simp only [slope, original, div_eq_mul_inv, smul_eq_mul, vsub_eq_sub,
    mul_sub]
  ring

theorem gap1 (a : ℝ) (ha : 0 < a) (L : ℝ) :
    HasLimitAt (original a) a L ↔ HasLimitAt (quotientLog a) a L := by
  have hpos : ∀ᶠ x : ℝ in nhdsWithin a ({a} : Set ℝ)ᶜ, 0 < x :=
    (eventually_gt_nhds ha).filter_mono inf_le_left
  have heq : original a =ᶠ[nhdsWithin a ({a} : Set ℝ)ᶜ] quotientLog a := by
    filter_upwards [hpos] with x hx
    simp only [original, quotientLog]
    rw [Real.log_div hx.ne' ha.ne']
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Exercise 531, gap 2. -/
theorem gap2 (a : ℝ) (ha : 0 < a) (L : ℝ) :
    HasLimitAt (quotientLog a) a L ↔ HasLimitAt (rewritten a) a L := by
  have hpos : ∀ᶠ x : ℝ in nhdsWithin a ({a} : Set ℝ)ᶜ, 0 < x :=
    (eventually_gt_nhds ha).filter_mono inf_le_left
  have heq : quotientLog a =ᶠ[nhdsWithin a ({a} : Set ℝ)ᶜ] rewritten a := by
    filter_upwards [hpos, self_mem_nhdsWithin] with x hx hxmem
    have hne : x ≠ a := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxmem
    have hsub : x - a ≠ 0 := sub_ne_zero.mpr hne
    have hbase : 1 + 1 / (a / (x - a)) = x / a := by
      field_simp [ha.ne', hsub] <;> ring
    have hexp : (a / (x - a)) * (1 / a) = 1 / (x - a) := by
      field_simp [ha.ne', hsub] <;> ring
    simp only [quotientLog, rewritten]
    rw [hbase, hexp]
    change Real.log (x / a) / (x - a) =
      Real.log ((x / a) ^ (1 / (x - a)))
    rw [Real.log_rpow (div_pos hx ha)]
    ring
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Exercise 531, gap 3. -/
theorem gap3 (a : ℝ) (ha : 0 < a) :
    HasLimitAt (rewritten a) a (Real.log (Real.exp (1 / a))) := by
  have hrew : HasLimitAt (rewritten a) a (1 / a) :=
    (gap2 a ha (1 / a)).mp
      ((gap1 a ha (1 / a)).mp (originalLimitAt a ha))
  simpa only [Real.log_exp] using hrew

/-- Exercise 531, gap 4. -/
theorem gap4 (a : ℝ) (ha : 0 < a) :
    Real.log (Real.exp (1 / a)) = 1 / a := by
  exact Real.log_exp (1 / a)

/-- Exercise 531, gap 5. -/
theorem gap5 (a : ℝ) (ha : 0 < a) :
    HasLimitAt (original a) a (1 / a) := by
  exact originalLimitAt a ha

end

end ProofGap.Exercise531
