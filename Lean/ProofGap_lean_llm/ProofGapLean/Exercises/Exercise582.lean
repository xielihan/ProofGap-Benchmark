import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise582

noncomputable section

def original (x : ℝ) : ℝ := Real.arccos (Real.sqrt (x ^ 2 + x) - x)
def rationalized (x : ℝ) : ℝ :=
  Real.arccos (x / (Real.sqrt (x ^ 2 + x) + x))
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Source: `proof_gap/exercise_582/1.txt`. -/
theorem gap1 (L : ℝ) :
    HasLimitAtPosInfinity original L ↔ HasLimitAtPosInfinity rationalized L := by
  unfold HasLimitAtPosInfinity
  have h_eq : original =ᶠ[Filter.atTop] rationalized := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    unfold original rationalized
    apply congrArg Real.arccos
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hrad : 0 ≤ x ^ 2 + x := by
      nlinarith [sq_nonneg x]
    have hs_sq : (Real.sqrt (x ^ 2 + x)) ^ 2 = x ^ 2 + x :=
      Real.sq_sqrt hrad
    have hden : 0 < Real.sqrt (x ^ 2 + x) + x := by
      nlinarith [Real.sqrt_nonneg (x ^ 2 + x)]
    apply (eq_div_iff (ne_of_gt hden)).2
    calc
      (Real.sqrt (x ^ 2 + x) - x) *
          (Real.sqrt (x ^ 2 + x) + x) =
          (Real.sqrt (x ^ 2 + x)) ^ 2 - x ^ 2 := by ring
      _ = x := by rw [hs_sq]; ring
  constructor
  · intro h
    exact Filter.Tendsto.congr' h_eq h
  · intro h
    exact Filter.Tendsto.congr' h_eq.symm h

/-- Source: `proof_gap/exercise_582/2.txt`. -/
theorem gap2 : HasLimitAtPosInfinity rationalized (Real.arccos (1 / 2)) := by
  unfold HasLimitAtPosInfinity rationalized
  have hinv :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have harg :
      Filter.Tendsto (fun x : ℝ => 1 + x⁻¹) Filter.atTop (nhds 1) := by
    simpa using
      ((tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1)).add hinv)
  have hsqrt :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 + x⁻¹))
        Filter.atTop (nhds 1) := by
    simpa using ((Real.continuous_sqrt.tendsto (1 : ℝ)).comp harg)
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have hdenlim :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 + x⁻¹) + 1)
        Filter.atTop (nhds 2) := by
    convert hsqrt.add hone using 1 <;> norm_num
  have hform :
      Filter.Tendsto
        (fun x : ℝ => 1 / (Real.sqrt (1 + x⁻¹) + 1))
        Filter.atTop (nhds (1 / 2)) := by
    change Filter.Tendsto
      ((fun _ : ℝ => (1 : ℝ)) /
        (fun x : ℝ => Real.sqrt (1 + x⁻¹) + 1))
      Filter.atTop (nhds ((1 : ℝ) / 2))
    exact hone.div hdenlim (by norm_num : (2 : ℝ) ≠ 0)
  have h_eq :
      (fun x : ℝ => 1 / (Real.sqrt (1 + x⁻¹) + 1)) =ᶠ[Filter.atTop]
        (fun x : ℝ => x / (Real.sqrt (x ^ 2 + x) + x)) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hradpos : 0 < x ^ 2 + x := by
      nlinarith [sq_nonneg x]
    have hrad : 0 ≤ x ^ 2 + x := le_of_lt hradpos
    have hrad' : 0 ≤ 1 + x⁻¹ :=
      add_nonneg (by norm_num) (le_of_lt (inv_pos.mpr hxpos))
    have hs_sq : (Real.sqrt (x ^ 2 + x)) ^ 2 = x ^ 2 + x :=
      Real.sq_sqrt hrad
    have ht_sq : (Real.sqrt (1 + x⁻¹)) ^ 2 = 1 + x⁻¹ :=
      Real.sq_sqrt hrad'
    have ht_rel : x * (Real.sqrt (1 + x⁻¹)) ^ 2 = x + 1 := by
      calc
        x * (Real.sqrt (1 + x⁻¹)) ^ 2 = x * (1 + x⁻¹) := by rw [ht_sq]
        _ = x + x * x⁻¹ := by ring
        _ = x + 1 := by simp [ne_of_gt hxpos]
    have hxt_sq :
        (x * Real.sqrt (1 + x⁻¹)) ^ 2 = x ^ 2 + x := by
      calc
        (x * Real.sqrt (1 + x⁻¹)) ^ 2 =
            x * (x * (Real.sqrt (1 + x⁻¹)) ^ 2) := by ring
        _ = x * (x + 1) := by rw [ht_rel]
        _ = x ^ 2 + x := by ring
    have hxt_nonneg : 0 ≤ x * Real.sqrt (1 + x⁻¹) :=
      mul_nonneg (le_of_lt hxpos) (Real.sqrt_nonneg (1 + x⁻¹))
    have hscale :
        Real.sqrt (x ^ 2 + x) = x * Real.sqrt (1 + x⁻¹) := by
      have hprod :
          (Real.sqrt (x ^ 2 + x) - x * Real.sqrt (1 + x⁻¹)) *
              (Real.sqrt (x ^ 2 + x) + x * Real.sqrt (1 + x⁻¹)) = 0 := by
        calc
          (Real.sqrt (x ^ 2 + x) - x * Real.sqrt (1 + x⁻¹)) *
              (Real.sqrt (x ^ 2 + x) + x * Real.sqrt (1 + x⁻¹)) =
              (Real.sqrt (x ^ 2 + x)) ^ 2 -
                (x * Real.sqrt (1 + x⁻¹)) ^ 2 := by ring
          _ = 0 := by rw [hs_sq, hxt_sq]; ring
      have hsumpos :
          0 < Real.sqrt (x ^ 2 + x) + x * Real.sqrt (1 + x⁻¹) :=
        add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 hradpos) hxt_nonneg
      rcases mul_eq_zero.mp hprod with hdiff | hsum
      · exact sub_eq_zero.mp hdiff
      · exact False.elim ((ne_of_gt hsumpos) hsum)
    have htden : Real.sqrt (1 + x⁻¹) + 1 ≠ 0 := by
      apply ne_of_gt
      nlinarith [Real.sqrt_nonneg (1 + x⁻¹)]
    have hden2 : x * Real.sqrt (1 + x⁻¹) + x ≠ 0 := by
      apply ne_of_gt
      nlinarith [hxt_nonneg]
    rw [hscale]
    field_simp [htden, hden2] <;> ring
  have hratio :
      Filter.Tendsto
        (fun x : ℝ => x / (Real.sqrt (x ^ 2 + x) + x))
        Filter.atTop (nhds (1 / 2)) :=
    Filter.Tendsto.congr' h_eq hform
  exact (Real.continuous_arccos.tendsto (1 / 2)).comp hratio

/-- Source: `proof_gap/exercise_582/3.txt`. -/
theorem gap3 : Real.arccos (1 / 2) = Real.pi / 3 := by
  calc
    Real.arccos (1 / 2) =
        Real.arccos (Real.cos (Real.pi / 3)) := by
      rw [Real.cos_pi_div_three]
    _ = Real.pi / 3 :=
      Real.arccos_cos
        (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])

/-- Source: `proof_gap/exercise_582/4.txt`. -/
theorem gap4 : HasLimitAtPosInfinity original (Real.pi / 3) := by
  apply (gap1 (Real.pi / 3)).2
  rw [← gap3]
  exact gap2

end

end ProofGap.Exercise582
