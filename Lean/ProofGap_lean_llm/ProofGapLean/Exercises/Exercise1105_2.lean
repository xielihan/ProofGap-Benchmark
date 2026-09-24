import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1105_2

noncomputable section

def nthRoot (n : ℕ) (x : ℝ) : ℝ :=
  Real.rpow x (1 / (n : ℝ))

def Approx (x y ε : ℝ) : Prop := |x - y| < ε

private theorem nthRoot_power_facts (n : ℕ) (a : ℝ) (hn : 0 < n) (ha : 0 < a) :
    nthRoot n (a ^ n) = a ∧
      nthRoot n ((a ^ n) ^ (n - 1)) = a ^ (n - 1) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  constructor
  · unfold nthRoot
    calc
      Real.rpow (a ^ n) (1 / (n : ℝ)) =
          Real.exp (Real.log (a ^ n) * (1 / (n : ℝ))) :=
        Real.rpow_def_of_pos (pow_pos ha n) (1 / (n : ℝ))
      _ = Real.exp (Real.log a) := by
        rw [Real.log_pow]
        congr 1
        field_simp
      _ = a := Real.exp_log ha
  · unfold nthRoot
    calc
      Real.rpow ((a ^ n) ^ (n - 1)) (1 / (n : ℝ)) =
          Real.exp (Real.log ((a ^ n) ^ (n - 1)) * (1 / (n : ℝ))) :=
        Real.rpow_def_of_pos (pow_pos (pow_pos ha n) (n - 1)) (1 / (n : ℝ))
      _ = Real.exp (Real.log (a ^ (n - 1))) := by
        congr 1
        rw [Real.log_pow, Real.log_pow, Real.log_pow]
        rw [Nat.cast_sub hn]
        field_simp
        <;> ring
      _ = a ^ (n - 1) := Real.exp_log (pow_pos ha (n - 1))

theorem gap1 (n : ℕ) (a : ℝ) (hn : 0 < n) (ha : 0 < a) :
    HasDerivAt (fun x : ℝ => nthRoot n (a ^ n + x))
      (1 / ((n : ℝ) * nthRoot n ((a ^ n) ^ (n - 1)))) 0 := by
  have hfacts := nthRoot_power_facts n a hn ha
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hb : 0 < a ^ n := pow_pos ha n
  have hinner : HasDerivAt (fun x : ℝ => a ^ n + x) 1 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) 0).const_add (a ^ n)
  have hb0 : a ^ n + 0 ≠ 0 := by
    simpa using hb.ne'
  have hlogRaw := (Real.hasDerivAt_log hb0).comp 0 hinner
  have hlog : HasDerivAt (fun x : ℝ => Real.log (a ^ n + x)) (a ^ n)⁻¹ 0 := by
    simpa using hlogRaw
  have hmul := hlog.mul_const (1 / (n : ℝ))
  have hexpRaw :=
    (Real.hasDerivAt_exp (Real.log (a ^ n + 0) * (1 / (n : ℝ)))).comp 0 hmul
  have hexp :
      HasDerivAt
        (fun x : ℝ => Real.exp (Real.log (a ^ n + x) * (1 / (n : ℝ))))
        (Real.exp (Real.log (a ^ n) * (1 / (n : ℝ))) *
          ((a ^ n)⁻¹ * (1 / (n : ℝ)))) 0 := by
    simpa using hexpRaw
  have hevent : ∀ᶠ x : ℝ in nhds 0, 0 < a ^ n + x :=
    hinner.continuousAt
      (Ioi_mem_nhds (show 0 < a ^ n + 0 by simpa using hb))
  have heq :
      (fun x : ℝ => Real.exp (Real.log (a ^ n + x) * (1 / (n : ℝ)))) =ᶠ[nhds 0]
        (fun x : ℝ => nthRoot n (a ^ n + x)) := by
    filter_upwards [hevent] with x hx
    exact (Real.rpow_def_of_pos hx (1 / (n : ℝ))).symm
  have hrpow := hexp.congr_of_eventuallyEq heq.symm
  have hexpval : Real.exp (Real.log (a ^ n) * (1 / (n : ℝ))) = a := by
    calc
      Real.exp (Real.log (a ^ n) * (1 / (n : ℝ))) =
          Real.rpow (a ^ n) (1 / (n : ℝ)) :=
        (Real.rpow_def_of_pos hb (1 / (n : ℝ))).symm
      _ = a := hfacts.1
  have hpow : a ^ n = a ^ (n - 1) * a := by
    calc
      a ^ n = a ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hn]
      _ = a ^ (n - 1) * a := by rw [pow_succ]
  have hcoef :
      Real.exp (Real.log (a ^ n) * (1 / (n : ℝ))) *
          ((a ^ n)⁻¹ * (1 / (n : ℝ))) =
        1 / ((n : ℝ) * nthRoot n ((a ^ n) ^ (n - 1))) := by
    rw [hexpval, hfacts.2, hpow]
    field_simp [hn0, ne_of_gt ha, ne_of_gt (pow_pos ha (n - 1))]
    <;> ring
  simpa only [hcoef] using hrpow

theorem gap2 (n : ℕ) (a x : ℝ) (hn : 0 < n) (ha : 0 < a) :
    nthRoot n (a ^ n) +
        x / ((n : ℝ) * nthRoot n ((a ^ n) ^ (n - 1))) =
      a + x / ((n : ℝ) * a ^ (n - 1)) := by
  have hfacts := nthRoot_power_facts n a hn ha
  rw [hfacts.1, hfacts.2]

theorem gap3 (n : ℕ) (a : ℝ) (hn : 0 < n) (ha : 0 < a) :
    HasDerivAt (fun x : ℝ => nthRoot n (a ^ n + x))
      (1 / ((n : ℝ) * a ^ (n - 1))) 0 := by
  have hfacts := nthRoot_power_facts n a hn ha
  simpa only [hfacts.2] using gap1 n a hn ha

theorem gap4 :
    nthRoot 4 80 = nthRoot 4 (3 ^ 4 - 1) := by
  norm_num

theorem gap5 :
    Approx (nthRoot 4 (3 ^ 4 - 1))
      (3 - (1 / (4 * 3 ^ 3) : ℝ)) (1 / 10000 : ℝ) := by
  unfold Approx nthRoot
  norm_num [Real.rpow_def_of_pos]
  have hloPos : (0 : ℝ) < 323 / 108 - 1 / 10000 := by norm_num
  have hhiPos : (0 : ℝ) < 323 / 108 + 1 / 10000 := by norm_num
  have hlo :
      Real.log (323 / 108 - 1 / 10000 : ℝ) < Real.log 80 * (1 / 4) := by
    have h :
        4 * Real.log (323 / 108 - 1 / 10000 : ℝ) < Real.log 80 := by
      calc
        4 * Real.log (323 / 108 - 1 / 10000 : ℝ) =
            Real.log ((323 / 108 - 1 / 10000 : ℝ) ^ 4) := by
          rw [Real.log_pow]
          norm_num
        _ < Real.log 80 := by
          apply Real.strictMonoOn_log
          · norm_num
          · norm_num
          · norm_num
    linarith
  have hhi :
      Real.log 80 * (1 / 4) < Real.log (323 / 108 + 1 / 10000 : ℝ) := by
    have h :
        Real.log 80 < 4 * Real.log (323 / 108 + 1 / 10000 : ℝ) := by
      calc
        Real.log 80 < Real.log ((323 / 108 + 1 / 10000 : ℝ) ^ 4) := by
          apply Real.strictMonoOn_log
          · norm_num
          · norm_num
          · norm_num
        _ = 4 * Real.log (323 / 108 + 1 / 10000 : ℝ) := by
          rw [Real.log_pow]
          norm_num
    linarith
  rw [abs_lt]
  constructor
  · have h := Real.exp_lt_exp.mpr hlo
    rw [Real.exp_log hloPos] at h
    linarith
  · have h := Real.exp_lt_exp.mpr hhi
    rw [Real.exp_log hhiPos] at h
    linarith

theorem gap6 :
    Approx (3 - (1 / (4 * 3 ^ 3) : ℝ))
      (29907 / 10000 : ℝ) (1 / 10000 : ℝ) := by
  unfold Approx
  norm_num [abs_lt]

theorem gap7 :
    Approx (nthRoot 4 80) (29907 / 10000 : ℝ)
      (1 / 10000 : ℝ) := by
  unfold Approx nthRoot
  norm_num [Real.rpow_def_of_pos]
  have hloPos : (0 : ℝ) < 29906 / 10000 := by norm_num
  have hhiPos : (0 : ℝ) < 29908 / 10000 := by norm_num
  have hlo :
      Real.log (29906 / 10000 : ℝ) < Real.log 80 * (1 / 4) := by
    have h : 4 * Real.log (29906 / 10000 : ℝ) < Real.log 80 := by
      calc
        4 * Real.log (29906 / 10000 : ℝ) =
            Real.log ((29906 / 10000 : ℝ) ^ 4) := by
          rw [Real.log_pow]
          norm_num
        _ < Real.log 80 := by
          apply Real.strictMonoOn_log
          · norm_num
          · norm_num
          · norm_num
    linarith
  have hhi :
      Real.log 80 * (1 / 4) < Real.log (29908 / 10000 : ℝ) := by
    have h : Real.log 80 < 4 * Real.log (29908 / 10000 : ℝ) := by
      calc
        Real.log 80 < Real.log ((29908 / 10000 : ℝ) ^ 4) := by
          apply Real.strictMonoOn_log
          · norm_num
          · norm_num
          · norm_num
        _ = 4 * Real.log (29908 / 10000 : ℝ) := by
          rw [Real.log_pow]
          norm_num
    linarith
  rw [abs_lt]
  constructor
  · have h := Real.exp_lt_exp.mpr hlo
    rw [Real.exp_log hloPos] at h
    linarith
  · have h := Real.exp_lt_exp.mpr hhi
    rw [Real.exp_log hhiPos] at h
    linarith

theorem gap8 :
    Approx (nthRoot 4 80) (29905 / 10000 : ℝ)
      (3 / 10000 : ℝ) := by
  have h := gap7
  unfold Approx at h ⊢
  rw [abs_lt] at h ⊢
  rcases h with ⟨hlo, hhi⟩
  constructor <;> linarith

end

end ProofGap.Exercise1105_2
