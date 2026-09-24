import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise553

noncomputable section

def seq (x : ℝ) (n : ℕ) : ℝ :=
  n ^ 2 * (Real.rpow x (1 / (n : ℝ)) - Real.rpow x (1 / ((n : ℝ) + 1)))
def quotient (x : ℝ) (n : ℕ) : ℝ :=
  (Real.rpow x (1 / (n : ℝ)) - Real.rpow x (1 / ((n : ℝ) + 1))) /
    (1 / (n : ℝ) ^ 2)
def transformed (x : ℝ) (n : ℕ) : ℝ :=
  (Real.rpow x (1 / ((n : ℝ) + 1)) *
    (Real.rpow x (1 / ((n : ℝ) * ((n : ℝ) + 1))) - 1)) /
  (1 / ((n : ℝ) * ((n : ℝ) + 1)) + 1 / (n : ℝ) ^ 2 -
    1 / ((n : ℝ) ^ 2 + n))

/-- Source: `proof_gap/exercise_553/1.txt`. -/
theorem gap1 (x : ℝ) (hx : 0 < x) (L : ℝ) :
    Filter.Tendsto (seq x) Filter.atTop (nhds L) ↔
      Filter.Tendsto (quotient x) Filter.atTop (nhds L) := by
  have heq : seq x =ᶠ[Filter.atTop] quotient x := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ h => h⟩] with n hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.2 hnpos
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    unfold seq quotient
    field_simp [hn0] <;> ring
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Source: `proof_gap/exercise_553/2.txt`. -/
theorem gap2 (x : ℝ) (hx : 0 < x) (L : ℝ) :
    Filter.Tendsto (quotient x) Filter.atTop (nhds L) ↔
      Filter.Tendsto (transformed x) Filter.atTop (nhds L) := by
  have heq : quotient x =ᶠ[Filter.atTop] transformed x := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ h => h⟩] with n hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.2 hnpos
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hnp1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hnsum : (n : ℝ) ^ 2 + (n : ℝ) ≠ 0 := by positivity
    have hexp :
        1 / (n : ℝ) =
          1 / ((n : ℝ) + 1) +
            1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      field_simp [hn0, hnp1]
      <;> ring
    have hrpow :
        Real.rpow x (1 / (n : ℝ)) =
          Real.rpow x (1 / ((n : ℝ) + 1)) *
            Real.rpow x (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
      calc
        Real.rpow x (1 / (n : ℝ)) =
            Real.rpow x
              (1 / ((n : ℝ) + 1) +
                1 / ((n : ℝ) * ((n : ℝ) + 1))) :=
          congrArg (fun t : ℝ => Real.rpow x t) hexp
        _ = _ := Real.rpow_add hx _ _
    unfold quotient transformed
    rw [hrpow]
    field_simp [hn0, hnp1, hnsum]
    <;> ring
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Source: `proof_gap/exercise_553/3.txt`. -/
theorem gap3 (x : ℝ) (hx : 0 < x) :
    Filter.Tendsto (transformed x) Filter.atTop (nhds (Real.log x)) := by
  by_cases hx1 : x = 1
  · subst x
    have heq : transformed (1 : ℝ) = (fun _ : ℕ => (0 : ℝ)) := by
      funext n
      simp [transformed]
    rw [heq, Real.log_one]
    exact tendsto_const_nhds
  have hlogne : Real.log x ≠ 0 := by
    intro hlog
    apply hx1
    calc
      x = Real.exp (Real.log x) := (Real.exp_log hx).symm
      _ = 1 := by simp [hlog]
  have hq :
      Filter.Tendsto (fun n : ℕ => 1 / (n : ℝ)) Filter.atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop))
  have hone :
      Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have hbase :
      Filter.Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ))
        Filter.atTop (nhds 1) := by
    simpa using hone.add hq
  have hrecip :
      Filter.Tendsto (fun n : ℕ => (1 + 1 / (n : ℝ))⁻¹)
        Filter.atTop (nhds 1) := by
    simpa using hbase.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hvprod :
      Filter.Tendsto
        (fun n : ℕ => (1 / (n : ℝ)) * (1 + 1 / (n : ℝ))⁻¹)
        Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using hq.mul hrecip
  have hveq :
      (fun n : ℕ => (1 / (n : ℝ)) * (1 + 1 / (n : ℝ))⁻¹) =ᶠ[Filter.atTop]
        (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ h => h⟩] with n hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.2 hnpos
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    field_simp [hn0]
    <;> ring
  have hv :
      Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
        Filter.atTop (nhds 0) :=
    hvprod.congr' hveq
  have huprod :
      Filter.Tendsto
        (fun n : ℕ => (1 / (n : ℝ)) * (1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using hq.mul hv
  have hueq :
      (fun n : ℕ => (1 / (n : ℝ)) * (1 / ((n : ℝ) + 1))) =ᶠ[Filter.atTop]
        (fun n : ℕ => 1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ h => h⟩] with n hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.2 hnpos
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hnp1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn0, hnp1]
    <;> ring
  have hu :
      Filter.Tendsto
        (fun n : ℕ => 1 / ((n : ℝ) * ((n : ℝ) + 1)))
        Filter.atTop (nhds 0) :=
    huprod.congr' hueq
  have hlogconst :
      Filter.Tendsto (fun _ : ℕ => Real.log x) Filter.atTop
        (nhds (Real.log x)) :=
    tendsto_const_nhds
  have hlogv :
      Filter.Tendsto
        (fun n : ℕ => Real.log x * (1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds 0) := by
    simpa using hlogconst.mul hv
  have hA :
      Filter.Tendsto
        (fun n : ℕ => Real.rpow x (1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds 1) := by
    simpa [Real.rpow_def_of_pos hx] using
      (Real.continuous_exp.continuousAt.tendsto.comp hlogv)
  have hz :
      Filter.Tendsto
        (fun n : ℕ =>
          Real.log x * (1 / ((n : ℝ) * ((n : ℝ) + 1))))
        Filter.atTop (nhds 0) := by
    simpa using hlogconst.mul hu
  have hzne :
      ∀ᶠ n : ℕ in Filter.atTop,
        Real.log x * (1 / ((n : ℝ) * ((n : ℝ) + 1))) ≠ 0 := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ h => h⟩] with n hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.2 hnpos
    have hnp1 : 0 < (n : ℝ) + 1 := by positivity
    exact mul_ne_zero hlogne
      (one_div_ne_zero (mul_ne_zero (ne_of_gt hnR) (ne_of_gt hnp1)))
  have hzwithin :
      Filter.Tendsto
        (fun n : ℕ =>
          Real.log x * (1 / ((n : ℝ) * ((n : ℝ) + 1))))
        Filter.atTop (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hz, ?_⟩
    filter_upwards [hzne] with n hn
    simpa using hn
  have hslope :
      Filter.Tendsto (fun z : ℝ => (Real.exp z - 1) / z)
        (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_exp 0).tendsto_slope_zero
  have hB :
      Filter.Tendsto
        (fun n : ℕ =>
          (Real.exp
              (Real.log x *
                (1 / ((n : ℝ) * ((n : ℝ) + 1)))) - 1) /
            (Real.log x *
              (1 / ((n : ℝ) * ((n : ℝ) + 1)))))
        Filter.atTop (nhds 1) :=
    hslope.comp hzwithin
  have hCeq :
      (fun n : ℕ => (1 + 1 / (n : ℝ))⁻¹) =ᶠ[Filter.atTop]
        (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ h => h⟩] with n hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.2 hnpos
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hnp1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn0, hnp1]
    <;> ring
  have hC :
      Filter.Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (nhds 1) :=
    hrecip.congr' hCeq
  have hmain :
      Filter.Tendsto
        (fun n : ℕ =>
          Real.rpow x (1 / ((n : ℝ) + 1)) *
            (((Real.exp
                  (Real.log x *
                    (1 / ((n : ℝ) * ((n : ℝ) + 1)))) - 1) /
                (Real.log x *
                  (1 / ((n : ℝ) * ((n : ℝ) + 1)))) *
              Real.log x) *
            ((n : ℝ) / ((n : ℝ) + 1))))
        Filter.atTop (nhds (Real.log x)) := by
    simpa only [one_mul, mul_one] using
      hA.mul ((hB.mul hlogconst).mul hC)
  refine hmain.congr' ?_
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ h => h⟩] with n hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.2 hnpos
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hnp1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hnsum : (n : ℝ) ^ 2 + (n : ℝ) ≠ 0 := by positivity
  have hrpow :
      Real.rpow x (1 / ((n : ℝ) * ((n : ℝ) + 1))) =
        Real.exp
          (Real.log x * (1 / ((n : ℝ) * ((n : ℝ) + 1)))) := by
    simpa [Real.rpow_def_of_pos hx]
  unfold transformed
  rw [hrpow]
  field_simp [hn0, hnp1, hnsum, hlogne]
  <;> ring

end

end ProofGap.Exercise553
