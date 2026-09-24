import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1296_3

open Filter
open scoped Topology

noncomputable section

def powerMean (a b s : ℝ) : ℝ :=
  if s = 0 then Real.sqrt (a * b)
  else Real.rpow ((Real.rpow a s + Real.rpow b s) / 2) (1 / s)

def lowerFactor (a b s : ℝ) : ℝ :=
  a * Real.rpow ((1 / 2 : ℝ) +
    (1 / 2 : ℝ) * Real.rpow (b / a) s) (1 / s)

def upperFactor (a b s : ℝ) : ℝ :=
  b * Real.rpow ((1 / 2 : ℝ) * Real.rpow (a / b) s +
    (1 / 2 : ℝ)) (1 / s)

private theorem powerMean_eq_lower_of_ne
    (a b s : ℝ) (ha : 0 < a) (hb : 0 < b) (hs : s ≠ 0) :
    powerMean a b s = lowerFactor a b s := by
  have has : 0 < Real.rpow a s := Real.rpow_pos_of_pos ha s
  have hrs : 0 < Real.rpow (b / a) s :=
    Real.rpow_pos_of_pos (div_pos hb ha) s
  have hbase :
      0 < (1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.rpow (b / a) s := by
    positivity
  have hba : a * (b / a) = b := by
    field_simp [ne_of_gt ha]
  have hbpow :
      Real.rpow b s = Real.rpow a s * Real.rpow (b / a) s := by
    calc
      Real.rpow b s = Real.rpow (a * (b / a)) s := by rw [hba]
      _ = Real.rpow a s * Real.rpow (b / a) s := by
        exact Real.mul_rpow ha.le (div_nonneg hb.le ha.le)
  have hinside :
      (Real.rpow a s + Real.rpow b s) / 2 =
        Real.rpow a s *
          ((1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.rpow (b / a) s) := by
    rw [hbpow]
    ring
  have hcancel : s * (1 / s) = 1 := by
    field_simp [hs]
  have hnested :
      Real.rpow (Real.rpow a s) (1 / s) =
        Real.rpow a (s * (1 / s)) :=
    (Real.rpow_mul ha.le s (1 / s)).symm
  have hone : Real.rpow a (1 : ℝ) = a := by
    calc
      Real.rpow a (1 : ℝ) = Real.exp (Real.log a * 1) :=
        Real.rpow_def_of_pos ha 1
      _ = a := by rw [mul_one, Real.exp_log ha]
  simp only [powerMean, if_neg hs, lowerFactor]
  rw [hinside]
  calc
    Real.rpow
        (Real.rpow a s *
          ((1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.rpow (b / a) s))
        (1 / s) =
      Real.rpow (Real.rpow a s) (1 / s) *
        Real.rpow
          ((1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.rpow (b / a) s)
          (1 / s) := by
      exact Real.mul_rpow has.le hbase.le
    _ = a * Real.rpow
          ((1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.rpow (b / a) s)
          (1 / s) := by
      rw [hnested, hcancel, hone]

private theorem tendsto_variable_rpow_one
    {α : Type*} {l : Filter α} {u v : α → ℝ} {c : ℝ}
    (hc : 0 < c) (hu : Tendsto u l (𝓝 c)) (hv : Tendsto v l (𝓝 0)) :
    Tendsto (fun x => Real.rpow (u x) (v x)) l (𝓝 1) := by
  have hlogc :
      Tendsto Real.log (𝓝 c) (𝓝 (Real.log c)) :=
    Real.continuousAt_log (ne_of_gt hc)
  have hlog :
      Tendsto (fun x => Real.log (u x)) l (𝓝 (Real.log c)) :=
    hlogc.comp hu
  have hprod :
      Tendsto (fun x => Real.log (u x) * v x) l (𝓝 0) := by
    simpa only [mul_zero] using hlog.mul hv
  have hexpc :
      Tendsto Real.exp (𝓝 (0 : ℝ)) (𝓝 (Real.exp 0)) :=
    Real.continuous_exp.continuousAt
  have hexp :
      Tendsto (fun x => Real.exp (Real.log (u x) * v x)) l (𝓝 1) := by
    simpa only [Real.exp_zero] using hexpc.comp hprod
  refine (tendsto_congr' ?_).2 hexp
  filter_upwards [hu.eventually (Ioi_mem_nhds hc)] with x hx
  exact Real.rpow_def_of_pos hx (v x)

private theorem tendsto_rpow_atBot_of_one_lt (c : ℝ) (hc : 1 < c) :
    Tendsto (fun x : ℝ => Real.rpow c x) atBot (𝓝 0) := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hlog : 0 < Real.log c := Real.log_pos hc
  have hlinear :
      Tendsto (fun x : ℝ => Real.log c * x) atBot atBot := by
    refine tendsto_atBot.2 ?_
    intro z
    filter_upwards [eventually_le_atBot (z / Real.log c)] with x hx
    have hx' : x * Real.log c ≤ z := (le_div_iff₀ hlog).1 hx
    simpa [mul_comm] using hx'
  have hexp :
      Tendsto (fun x : ℝ => Real.exp (Real.log c * x)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlinear
  refine (tendsto_congr' ?_).2 hexp
  exact Filter.Eventually.of_forall (fun x => Real.rpow_def_of_pos hcpos x)

theorem gap1 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    (fun s => powerMean a b s) =ᶠ[atBot] (fun s => lowerFactor a b s) := by
  have hb : 0 < b := lt_trans ha hab
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with s hs
  exact powerMean_eq_lower_of_ne a b s ha hb (ne_of_lt hs)

theorem gap2 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto (lowerFactor a b) atBot (𝓝 a) := by
  have hratio : 1 < b / a := by
    apply (lt_div_iff₀ ha).2
    simpa using hab
  have hrpow :
      Tendsto (fun s : ℝ => Real.rpow (b / a) s) atBot (𝓝 0) :=
    tendsto_rpow_atBot_of_one_lt (b / a) hratio
  have hc :
      Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) atBot (𝓝 (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  have hbase :
      Tendsto
        (fun s : ℝ => (1 / 2 : ℝ) +
          (1 / 2 : ℝ) * Real.rpow (b / a) s)
        atBot (𝓝 (1 / 2 : ℝ)) := by
    simpa using hc.add (hc.mul hrpow)
  have hinv : Tendsto (fun s : ℝ => 1 / s) atBot (𝓝 0) := by
    simpa [one_div] using
      (tendsto_inv_atBot_zero :
        Tendsto (fun s : ℝ => s⁻¹) atBot (𝓝 0))
  have hpow := tendsto_variable_rpow_one
    (by norm_num : (0 : ℝ) < 1 / 2) hbase hinv
  change Tendsto
    (fun s : ℝ => a * Real.rpow
      ((1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.rpow (b / a) s) (1 / s))
    atBot (𝓝 a)
  simpa [one_div] using
    ((tendsto_const_nhds :
      Tendsto (fun _ : ℝ => a) atBot (𝓝 a)).mul hpow)

theorem gap3 (a b : ℝ) (hab : a < b) :
    a = min a b := by
  exact (min_eq_left (le_of_lt hab)).symm

theorem gap4 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto (powerMean a b) atBot (𝓝 (min a b)) := by
  rw [← gap3 a b hab]
  exact (tendsto_congr' (gap1 a b ha hab)).2 (gap2 a b ha hab)

theorem gap5 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    (fun s => powerMean a b s) =ᶠ[atTop] (fun s => upperFactor a b s) := by
  have hb : 0 < b := lt_trans ha hab
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  have h := powerMean_eq_lower_of_ne b a s hb ha (ne_of_gt hs)
  simpa [powerMean, lowerFactor, upperFactor, add_comm, mul_comm] using h

theorem gap6 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto (upperFactor a b) atTop (𝓝 b) := by
  have hb : 0 < b := lt_trans ha hab
  have hlarge : 1 < b / a := by
    apply (lt_div_iff₀ ha).2
    simpa using hab
  have hlarge_pos : 0 < b / a := lt_trans (by norm_num) hlarge
  have hsmall_pos : 0 < a / b := div_pos ha hb
  have hrecip : a / b = (b / a)⁻¹ := by
    field_simp [ne_of_gt ha, ne_of_gt hb]
  have hrpow_neg :
      Tendsto (fun s : ℝ => Real.rpow (b / a) (-s)) atTop (𝓝 0) :=
    (tendsto_rpow_atBot_of_one_lt (b / a) hlarge).comp
      tendsto_neg_atTop_atBot
  have heq :
      (fun s : ℝ => Real.rpow (a / b) s) =ᶠ[atTop]
        (fun s : ℝ => Real.rpow (b / a) (-s)) :=
    Filter.Eventually.of_forall (fun s => by
      calc
        Real.rpow (a / b) s =
            Real.exp (Real.log (a / b) * s) :=
          Real.rpow_def_of_pos hsmall_pos s
        _ = Real.exp (Real.log (b / a) * (-s)) := by
          rw [hrecip, Real.log_inv]
          congr 1
          ring
        _ = Real.rpow (b / a) (-s) :=
          (Real.rpow_def_of_pos hlarge_pos (-s)).symm)
  have hrpow :
      Tendsto (fun s : ℝ => Real.rpow (a / b) s) atTop (𝓝 0) :=
    (tendsto_congr' heq).2 hrpow_neg
  have hc :
      Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  have hbase :
      Tendsto
        (fun s : ℝ => (1 / 2 : ℝ) * Real.rpow (a / b) s +
          (1 / 2 : ℝ))
        atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using (hc.mul hrpow).add hc
  have hinv : Tendsto (fun s : ℝ => 1 / s) atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero :
        Tendsto (fun s : ℝ => s⁻¹) atTop (𝓝 0))
  have hpow := tendsto_variable_rpow_one
    (by norm_num : (0 : ℝ) < 1 / 2) hbase hinv
  change Tendsto
    (fun s : ℝ => b * Real.rpow
      ((1 / 2 : ℝ) * Real.rpow (a / b) s + (1 / 2 : ℝ)) (1 / s))
    atTop (𝓝 b)
  simpa [one_div] using
    ((tendsto_const_nhds :
      Tendsto (fun _ : ℝ => b) atTop (𝓝 b)).mul hpow)

theorem gap7 (a b : ℝ) (hab : a < b) :
    b = max a b := by
  exact (max_eq_right (le_of_lt hab)).symm

theorem gap8 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto (powerMean a b) atTop (𝓝 (max a b)) := by
  rw [← gap7 a b hab]
  exact (tendsto_congr' (gap5 a b ha hab)).2 (gap6 a b ha hab)

theorem gap9 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (powerMean a b) atBot (𝓝 (min a b)) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact gap4 a b ha hab
  · subst b
    have hev :
        (fun s => powerMean a a s) =ᶠ[atBot] (fun _ => a) := by
      filter_upwards [eventually_lt_atBot (0 : ℝ)] with s hs
      calc
        powerMean a a s = lowerFactor a a s :=
          powerMean_eq_lower_of_ne a a s ha ha (ne_of_lt hs)
        _ = a := by
          norm_num [lowerFactor, div_self (ne_of_gt ha)]
    simpa using
      (tendsto_congr' hev).2
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => a) atBot (𝓝 a))
  · have hev :
        (fun s => powerMean a b s) =ᶠ[atBot]
          (fun s => powerMean b a s) :=
      Filter.Eventually.of_forall (fun s => by
        simp [powerMean, add_comm, mul_comm])
    rw [min_comm]
    exact (tendsto_congr' hev).2 (gap4 b a hb hab)

theorem gap10 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (powerMean a b) atTop (𝓝 (max a b)) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact gap8 a b ha hab
  · subst b
    have hev :
        (fun s => powerMean a a s) =ᶠ[atTop] (fun _ => a) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
      calc
        powerMean a a s = lowerFactor a a s :=
          powerMean_eq_lower_of_ne a a s ha ha (ne_of_gt hs)
        _ = a := by
          norm_num [lowerFactor, div_self (ne_of_gt ha)]
    simpa using
      (tendsto_congr' hev).2
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => a) atTop (𝓝 a))
  · have hev :
        (fun s => powerMean a b s) =ᶠ[atTop]
          (fun s => powerMean b a s) :=
      Filter.Eventually.of_forall (fun s => by
        simp [powerMean, add_comm, mul_comm])
    rw [max_comm]
    exact (tendsto_congr' hev).2 (gap8 b a hb hab)

theorem gap11 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (powerMean a b) atBot (𝓝 (min a b)) ∧
      Tendsto (powerMean a b) atTop (𝓝 (max a b)) := by
  exact ⟨gap9 a b ha hb, gap10 a b ha hb⟩

end

end ProofGap.Exercise1296_3
