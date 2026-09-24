import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1453

noncomputable section

def f (x : ℝ) : ℝ := Real.exp (-x ^ 2) * Real.cos (x ^ 2)
def minimizer : ℝ := Real.sqrt (3 * Real.pi / 4)
def minimumValue : ℝ := -(Real.sqrt 2 / 2) * Real.exp (-(3 * Real.pi / 4))
def Approx (a b ε : ℝ) : Prop := |a - b| < ε

private theorem minimizer_value : f minimizer = minimumValue := by
  have ha : 0 ≤ 3 * Real.pi / 4 := by positivity
  have hs : (Real.sqrt (3 * Real.pi / 4)) ^ 2 = 3 * Real.pi / 4 :=
    Real.sq_sqrt ha
  unfold f minimizer minimumValue
  rw [hs]
  have hangle : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
  rw [hangle, Real.cos_sub, Real.cos_pi, Real.sin_pi,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  ring

private theorem damped_cos_lower (x : ℝ) : minimumValue ≤ f x := by
  let t : ℝ := x ^ 2
  let a : ℝ := 3 * Real.pi / 4
  let u : ℝ := t - a
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hu_lower : -a ≤ u := by
    dsimp [u]
    linarith
  have hpi4lt1 : Real.pi / 4 < 1 := by
    nlinarith [Real.pi_lt_d2]
  have henv : Real.cos u + Real.sin u ≤ Real.exp u := by
    by_cases hu : 0 ≤ u
    · have hsin := Real.sin_le hu
      have hcos := Real.cos_le_one u
      have hexp := Real.add_one_le_exp u
      linarith
    · have hu_neg : u < 0 := lt_of_not_ge hu
      by_cases hfar : u ≤ -(Real.pi / 4)
      · let v : ℝ := -u
        have hv_lower : Real.pi / 4 ≤ v := by
          dsimp [v]
          linarith
        have hv_upper : v ≤ 3 * Real.pi / 4 := by
          dsimp [v, a] at *
          linarith
        have hw_lower : Real.pi / 2 ≤ v + Real.pi / 4 := by linarith
        have hw_upper : v + Real.pi / 4 ≤ Real.pi + Real.pi / 2 := by
          linarith [Real.pi_pos]
        have hcw : Real.cos (v + Real.pi / 4) ≤ 0 :=
          Real.cos_nonpos_of_pi_div_two_le_of_le hw_lower hw_upper
        have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 :=
          Real.sq_sqrt (by norm_num)
        have hid : Real.cos v - Real.sin v =
            Real.sqrt 2 * Real.cos (v + Real.pi / 4) := by
          rw [Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four]
          ring_nf
          rw [hsqrt_sq]
          ring
        have hnonpos : Real.cos v - Real.sin v ≤ 0 := by
          rw [hid]
          exact mul_nonpos_of_nonneg_of_nonpos hsqrt hcw
        have huv : Real.cos u + Real.sin u = Real.cos v - Real.sin v := by
          dsimp [v]
          rw [Real.cos_neg, Real.sin_neg]
          ring
        rw [huv]
        exact hnonpos.trans (le_of_lt (Real.exp_pos u))
      · have hnear : -(Real.pi / 4) < u := lt_of_not_ge hfar
        let v : ℝ := -u
        have hv0 : 0 ≤ v := by
          dsimp [v]
          linarith
        have hvlt : v < Real.pi / 4 := by
          dsimp [v]
          linarith
        have hvltpi2 : v < Real.pi / 2 := by
          linarith [Real.pi_pos]
        have hcospos : 0 < Real.cos v := by
          apply Real.cos_pos_of_mem_Ioo
          constructor <;> linarith [Real.pi_pos]
        have htan : v ≤ Real.tan v := Real.le_tan hv0 hvltpi2
        rw [Real.tan_eq_sin_div_cos] at htan
        have hvsin : v * Real.cos v ≤ Real.sin v :=
          (le_div_iff₀ hcospos).mp htan
        have hv1 : v ≤ 1 := le_of_lt (hvlt.trans hpi4lt1)
        have hcosle : Real.cos v ≤ 1 := Real.cos_le_one v
        have htrig : Real.cos v - Real.sin v ≤ 1 - v := by
          calc
            Real.cos v - Real.sin v ≤ Real.cos v - v * Real.cos v :=
              sub_le_sub_left hvsin _
            _ = Real.cos v * (1 - v) := by ring
            _ ≤ 1 * (1 - v) :=
              mul_le_mul_of_nonneg_right hcosle (sub_nonneg.mpr hv1)
            _ = 1 - v := by ring
        have hexp : 1 - v ≤ Real.exp (-v) := by
          linarith [Real.add_one_le_exp (-v)]
        have huv : Real.cos u + Real.sin u = Real.cos v - Real.sin v := by
          dsimp [v]
          rw [Real.cos_neg, Real.sin_neg]
          ring
        have heu : Real.exp u = Real.exp (-v) := by
          congr 1
          dsimp [v]
          ring
        rw [huv, heu]
        exact htrig.trans hexp
  have hmul : Real.exp (-t) * (Real.cos u + Real.sin u) ≤ Real.exp (-a) := by
    have hp := mul_le_mul_of_nonneg_left henv (le_of_lt (Real.exp_pos (-t)))
    calc
      Real.exp (-t) * (Real.cos u + Real.sin u)
          ≤ Real.exp (-t) * Real.exp u := hp
      _ = Real.exp (-a) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [u]
        ring
  have hcost : Real.cos t =
      -(Real.sqrt 2 / 2) * (Real.cos u + Real.sin u) := by
    have htua : t = a + u := by
      dsimp [u]
      ring
    rw [htua, Real.cos_add]
    have haangle : a = Real.pi - Real.pi / 4 := by
      dsimp [a]
      ring
    rw [haangle, Real.cos_sub, Real.sin_sub, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
    ring
  have hc : 0 ≤ Real.sqrt 2 / 2 := by positivity
  unfold minimumValue f
  dsimp [t, a] at *
  calc
    -(Real.sqrt 2 / 2) * Real.exp (-(3 * Real.pi / 4))
        ≤ -(Real.sqrt 2 / 2) *
            (Real.exp (-(x ^ 2)) * (Real.cos u + Real.sin u)) :=
      mul_le_mul_of_nonpos_left hmul (neg_nonpos.mpr hc)
    _ = Real.exp (-(x ^ 2)) * Real.cos (x ^ 2) := by
      rw [hcost]
      ring

private theorem minimum_magnitude_bounds :
    (66 / 1000 : ℝ) <
        Real.sqrt 2 / 2 * Real.exp (-(3 * Real.pi / 4)) ∧
      Real.sqrt 2 / 2 * Real.exp (-(3 * Real.pi / 4)) <
        (68 / 1000 : ℝ) := by
  let a : ℝ := 3 * Real.pi / 4
  let y : ℝ := a / 512
  have ha_lower : (471 / 200 : ℝ) < a := by
    dsimp [a]
    nlinarith [Real.pi_gt_d2]
  have ha_upper : a < (189 / 80 : ℝ) := by
    dsimp [a]
    nlinarith [Real.pi_lt_d2]
  have hy_lower : (471 / 102400 : ℝ) < y := by
    dsimp [y]
    nlinarith
  have hy_upper : y < (189 / 40960 : ℝ) := by
    dsimp [y]
    nlinarith
  have hy_nonneg : 0 ≤ y := by linarith
  have hy_one : y < 1 := by linarith
  have hey_lower : (1 + 471 / 102400 : ℝ) < Real.exp y := by
    nlinarith [Real.add_one_le_exp y]
  have hey_upper : Real.exp y < (40960 / 40771 : ℝ) := by
    have h := Real.exp_bound_div_one_sub_of_interval hy_nonneg hy_one
    calc
      Real.exp y ≤ 1 / (1 - y) := h
      _ < (40960 / 40771 : ℝ) := by
        apply (div_lt_iff₀ (by linarith : 0 < 1 - y)).2
        norm_num
        nlinarith
  have heq : Real.exp a = Real.exp y ^ (512 : ℕ) := by
    calc
      Real.exp a = Real.exp ((((512 : ℕ) : ℝ)) * y) := by
        congr 1
        dsimp [y]
        ring
      _ = Real.exp y ^ (512 : ℕ) := by
        simpa using (Real.exp_nat_mul y 512)
  have hea_lower : (125 / 12 : ℝ) < Real.exp a := by
    rw [heq]
    calc
      (125 / 12 : ℝ) < (1 + 471 / 102400 : ℝ) ^ (512 : ℕ) := by
        set_option maxHeartbeats 2000000 in
          set_option maxRecDepth 4096 in
            norm_num [pow_succ]
      _ < Real.exp y ^ (512 : ℕ) := by gcongr
  have hea_upper : Real.exp a < (107 / 10 : ℝ) := by
    rw [heq]
    calc
      Real.exp y ^ (512 : ℕ) < (40960 / 40771 : ℝ) ^ (512 : ℕ) := by
        gcongr
      _ < (107 / 10 : ℝ) := by
        set_option maxHeartbeats 2000000 in
          set_option maxRecDepth 4096 in
            norm_num [pow_succ]
  have hprod : Real.exp a * Real.exp (-a) = 1 := by
    calc
      Real.exp a * Real.exp (-a) = Real.exp (a + -a) :=
        (Real.exp_add a (-a)).symm
      _ = 1 := by norm_num
  have hza : (10 / 107 : ℝ) < Real.exp (-a) := by
    have hm : Real.exp a * Real.exp (-a) <
        (107 / 10 : ℝ) * Real.exp (-a) :=
      mul_lt_mul_of_pos_right hea_upper (Real.exp_pos _)
    nlinarith
  have hzb : Real.exp (-a) < (12 / 125 : ℝ) := by
    have hm : (125 / 12 : ℝ) * Real.exp (-a) <
        Real.exp a * Real.exp (-a) :=
      mul_lt_mul_of_pos_right hea_lower (Real.exp_pos _)
    nlinarith
  have hs_lower : (140 / 99 : ℝ) < Real.sqrt 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hn := Real.sqrt_nonneg 2
    nlinarith
  have hs_upper : Real.sqrt 2 < (99 / 70 : ℝ) := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hn := Real.sqrt_nonneg 2
    nlinarith
  dsimp [a] at hza hzb
  constructor
  · calc
      (66 / 1000 : ℝ) < (70 / 99 : ℝ) * (10 / 107 : ℝ) := by norm_num
      _ < Real.sqrt 2 / 2 * Real.exp (-(3 * Real.pi / 4)) := by
        have hs : (70 / 99 : ℝ) < Real.sqrt 2 / 2 := by nlinarith
        exact mul_lt_mul hs (le_of_lt hza) (by norm_num) (by positivity)
  · calc
      Real.sqrt 2 / 2 * Real.exp (-(3 * Real.pi / 4))
          < (99 / 140 : ℝ) * (12 / 125 : ℝ) := by
        have hs : Real.sqrt 2 / 2 < (99 / 140 : ℝ) := by nlinarith
        exact mul_lt_mul hs (le_of_lt hzb) (Real.exp_pos _) (by norm_num)
      _ < (68 / 1000 : ℝ) := by norm_num

theorem gap1 :
    IsMinOn f Set.univ minimizer ∧ IsMinOn f Set.univ (-minimizer) := by
  constructor
  · intro x hx
    rw [minimizer_value]
    exact damped_cos_lower x
  · intro x hx
    have hneg : f (-minimizer) = minimumValue := by
      simpa [f] using minimizer_value
    rw [hneg]
    exact damped_cos_lower x

theorem gap2 : sInf (Set.range f) = f minimizer := by
  apply le_antisymm
  · apply csInf_le
    · refine ⟨f minimizer, ?_⟩
      rintro y ⟨x, rfl⟩
      exact gap1.1 (Set.mem_univ x)
    · exact ⟨minimizer, rfl⟩
  · apply le_csInf
    · exact Set.range_nonempty f
    · rintro y ⟨x, rfl⟩
      exact gap1.1 (Set.mem_univ x)

theorem gap3 :
    f minimizer = minimumValue ∧ f (-minimizer) = minimumValue := by
  constructor
  · exact minimizer_value
  · simpa [f] using minimizer_value

theorem gap4 : Approx minimumValue (-0.067) 0.001 := by
  unfold Approx minimumValue
  rw [abs_lt]
  constructor
  · nlinarith [minimum_magnitude_bounds.2]
  · nlinarith [minimum_magnitude_bounds.1]

theorem gap5 : Approx (sInf (Set.range f)) (-0.067) 0.001 := by
  rw [gap2, gap3.1]
  exact gap4

theorem gap6 : IsMaxOn f Set.univ 0 := by
  intro x hx
  have hepos : 0 < Real.exp (-x ^ 2) := Real.exp_pos _
  have hele : Real.exp (-x ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (sq_nonneg x)
  have hcos : Real.cos (x ^ 2) ≤ 1 := Real.cos_le_one _
  by_cases hc : 0 ≤ Real.cos (x ^ 2)
  · have hm : Real.exp (-x ^ 2) * Real.cos (x ^ 2) ≤ 1 := by
      calc
        Real.exp (-x ^ 2) * Real.cos (x ^ 2)
            ≤ 1 * Real.cos (x ^ 2) :=
          mul_le_mul_of_nonneg_right hele hc
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hcos (by norm_num)
        _ = 1 := by ring
    simpa [f] using hm
  · have hm : Real.exp (-x ^ 2) * Real.cos (x ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hepos) (le_of_not_ge hc)
    have hle : Real.exp (-x ^ 2) * Real.cos (x ^ 2) ≤ 1 := by linarith
    simpa [f] using hle

theorem gap7 : sSup (Set.range f) = f 0 := by
  apply le_antisymm
  · apply csSup_le
    · exact Set.range_nonempty f
    · rintro y ⟨x, rfl⟩
      exact gap6 (Set.mem_univ x)
  · apply le_csSup
    · refine ⟨f 0, ?_⟩
      rintro y ⟨x, rfl⟩
      exact gap6 (Set.mem_univ x)
    · exact ⟨0, rfl⟩

theorem gap8 : f 0 = 1 := by
  norm_num [f]

theorem gap9 : sSup (Set.range f) = 1 := by
  rw [gap7, gap8]

theorem gap10 : sInf (Set.range f) = minimumValue := by
  rw [gap2]
  exact gap3.1

theorem gap11 : sSup (Set.range f) = 1 := by
  exact gap9

end
end ProofGap.Exercise1453
