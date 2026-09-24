import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped Interval

namespace ProofGap.Exercise2532

noncomputable section

def mesh (i : ℕ) : ℝ := i / 8
def sample (i : ℕ) : ℝ := 1 / (1 + mesh i)
def interiorSum : ℝ := ∑ i ∈ Finset.Icc 1 7, sample i
def trapezoidApprox : ℝ :=
  (1 / 8 : ℝ) * ((sample 0 + sample 8) / 2 + interiorSum)
def exactIntegral : ℝ := ∫ x in (0 : ℝ)..1, 1 / (1 + x)
def remainder : ℝ := exactIntegral - trapezoidApprox

private theorem interiorSum_exact :
    interiorSum =
      8 / 9 + 4 / 5 + 8 / 11 + 2 / 3 + 8 / 13 + 4 / 7 + 8 / 15 := by
  have hset : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by
    decide
  rw [interiorSum, hset]
  norm_num [sample, mesh]

private theorem exactIntegral_eq_log_two : exactIntegral = Real.log 2 := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    have hi : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
      simpa using (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
    have hne : 1 + x ≠ 0 := by
      linarith [hx.1]
    simpa [one_div] using (Real.hasDerivAt_log hne).comp x hi
  have hcont : ContinuousOn (fun x : ℝ => 1 / (1 + x)) (Set.uIcc 0 1) := by
    apply ContinuousOn.div continuousOn_const
      (continuousOn_const.add continuousOn_id)
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    change (1 : ℝ) + x ≠ 0
    linarith [hx.1]
  have hint : IntervalIntegrable (fun x : ℝ => 1 / (1 + x)) MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable
  unfold exactIntegral
  convert intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint using 1 <;>
    norm_num

private theorem log_two_decimal_bounds :
    (0.69314 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.69316 := by
  let F : ℝ → ℝ := fun x => Real.log (1 + x) - Real.log (1 - x)
  let P : ℝ → ℝ := fun x =>
    2 * (x + x ^ 3 / 3 + x ^ 5 / 5 + x ^ 7 / 7 + x ^ 9 / 9)
  let Q : ℝ → ℝ := fun x => P x + (9 / 44 : ℝ) * x ^ 11
  have hF : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 3),
      HasDerivAt F (2 / (1 - x ^ 2)) x := by
    intro x hx
    have hp0 : 1 + x ≠ 0 := by linarith [hx.1]
    have hm0 : 1 - x ≠ 0 := by linarith [hx.2]
    have hden : 1 - x ^ 2 ≠ 0 := by
      rw [show 1 - x ^ 2 = (1 + x) * (1 - x) by ring]
      exact mul_ne_zero hp0 hm0
    have hiPlus : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
      simpa using (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
    have hiMinus : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    have hp : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
      simpa [one_div] using (Real.hasDerivAt_log hp0).comp x hiPlus
    have hm : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1 / (1 - x)) x := by
      convert (Real.hasDerivAt_log hm0).comp x hiMinus using 1 <;>
        simp [Function.comp_def, one_div] <;> ring
    dsimp [F]
    convert hp.sub hm using 1
    field_simp [hp0, hm0, hden]
    ring
  have hP : ∀ x : ℝ,
      HasDerivAt P (2 * (1 + x ^ 2 + x ^ 4 + x ^ 6 + x ^ 8)) x := by
    intro x
    have hs :=
      (hasDerivAt_id x).add (((hasDerivAt_id x).pow 3).div_const 3) |>.add
        (((hasDerivAt_id x).pow 5).div_const 5) |>.add
        (((hasDerivAt_id x).pow 7).div_const 7) |>.add
        (((hasDerivAt_id x).pow 9).div_const 9)
    have hp := (hasDerivAt_const x (2 : ℝ)).mul hs
    dsimp [P]
    convert hp using 1 <;> simp <;> ring
  have hQ : ∀ x : ℝ,
      HasDerivAt Q
        (2 * (1 + x ^ 2 + x ^ 4 + x ^ 6 + x ^ 8) +
          (9 / 4 : ℝ) * x ^ 10) x := by
    intro x
    have hr :=
      (hasDerivAt_const x (9 / 44 : ℝ)).mul ((hasDerivAt_id x).pow 11)
    dsimp [Q]
    convert (hP x).add hr using 1 <;> simp <;> ring
  let Dlow : ℝ → ℝ := fun x => F x - P x
  have hDlow : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 3),
      HasDerivAt Dlow (2 * x ^ 10 / (1 - x ^ 2)) x := by
    intro x hx
    have hplus : 0 < 1 + x := by linarith [hx.1]
    have hminus : 0 < 1 - x := by linarith [hx.2]
    have hdenpos : 0 < 1 - x ^ 2 := by
      nlinarith [mul_pos hplus hminus]
    have hden : 1 - x ^ 2 ≠ 0 := ne_of_gt hdenpos
    dsimp [Dlow]
    convert (hF x hx).sub (hP x) using 1
    field_simp [hden]
    ring
  have hDlowCont : ContinuousOn Dlow (Set.Icc (0 : ℝ) (1 / 3)) := by
    intro x hx
    exact (hDlow x hx).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcSlope⟩ :=
    exists_hasDerivAt_eq_slope (f := Dlow)
      (fun x => 2 * x ^ 10 / (1 - x ^ 2))
      (by norm_num : (0 : ℝ) < 1 / 3) hDlowCont
      (by
        intro x hx
        exact hDlow x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hcPlus : 0 < 1 + c := by linarith [hc.1]
  have hcMinus : 0 < 1 - c := by linarith [hc.2]
  have hcDen : 0 < 1 - c ^ 2 := by
    nlinarith [mul_pos hcPlus hcMinus]
  have hcDeriv : 0 < 2 * c ^ 10 / (1 - c ^ 2) := by
    have hcPow : 0 < c ^ 10 := pow_pos hc.1 10
    exact div_pos (mul_pos (by norm_num) hcPow) hcDen
  have hcEq :
      2 * c ^ 10 / (1 - c ^ 2) =
        3 * (Dlow (1 / 3) - Dlow 0) := by
    calc
      2 * c ^ 10 / (1 - c ^ 2) =
          (Dlow (1 / 3) - Dlow 0) / (1 / 3 - 0) := hcSlope
      _ = 3 * (Dlow (1 / 3) - Dlow 0) := by ring
  have hLowInc : Dlow 0 < Dlow (1 / 3) := by
    linarith [hcDeriv, hcEq]
  let Dup : ℝ → ℝ := fun x => Q x - F x
  have hDup : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 3),
      HasDerivAt Dup
        ((9 / 4 : ℝ) * x ^ 10 - 2 * x ^ 10 / (1 - x ^ 2)) x := by
    intro x hx
    have hplus : 0 < 1 + x := by linarith [hx.1]
    have hminus : 0 < 1 - x := by linarith [hx.2]
    have hdenpos : 0 < 1 - x ^ 2 := by
      nlinarith [mul_pos hplus hminus]
    have hden : 1 - x ^ 2 ≠ 0 := ne_of_gt hdenpos
    dsimp [Dup]
    convert (hQ x).sub (hF x hx) using 1
    field_simp [hden]
    ring
  have hDupCont : ContinuousOn Dup (Set.Icc (0 : ℝ) (1 / 3)) := by
    intro x hx
    exact (hDup x hx).continuousAt.continuousWithinAt
  obtain ⟨d, hd, hdSlope⟩ :=
    exists_hasDerivAt_eq_slope (f := Dup)
      (fun x => (9 / 4 : ℝ) * x ^ 10 - 2 * x ^ 10 / (1 - x ^ 2))
      (by norm_num : (0 : ℝ) < 1 / 3) hDupCont
      (by
        intro x hx
        exact hDup x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hdPlus : 0 < 1 + d := by linarith [hd.1]
  have hdMinus : 0 < 1 - d := by linarith [hd.2]
  have hdDen : 0 < 1 - d ^ 2 := by
    nlinarith [mul_pos hdPlus hdMinus]
  have hdNumLeft : 0 < 1 - 3 * d := by linarith [hd.2]
  have hdNumRight : 0 < 1 + 3 * d := by linarith [hd.1]
  have hdNum : 0 < 1 - 9 * d ^ 2 := by
    nlinarith [mul_pos hdNumLeft hdNumRight]
  have hdDeriv :
      0 < (9 / 4 : ℝ) * d ^ 10 - 2 * d ^ 10 / (1 - d ^ 2) := by
    have heq :
        (9 / 4 : ℝ) * d ^ 10 - 2 * d ^ 10 / (1 - d ^ 2) =
          d ^ 10 * (1 - 9 * d ^ 2) / (4 * (1 - d ^ 2)) := by
      field_simp [ne_of_gt hdDen]
      ring
    rw [heq]
    exact div_pos
      (mul_pos (pow_pos hd.1 10) hdNum)
      (mul_pos (by norm_num) hdDen)
  have hdEq :
      (9 / 4 : ℝ) * d ^ 10 - 2 * d ^ 10 / (1 - d ^ 2) =
        3 * (Dup (1 / 3) - Dup 0) := by
    calc
      (9 / 4 : ℝ) * d ^ 10 - 2 * d ^ 10 / (1 - d ^ 2) =
          (Dup (1 / 3) - Dup 0) / (1 / 3 - 0) := hdSlope
      _ = 3 * (Dup (1 / 3) - Dup 0) := by ring
  have hUpInc : Dup 0 < Dup (1 / 3) := by
    linarith [hdDeriv, hdEq]
  have hFzero : F 0 = 0 := by norm_num [F]
  have hPzero : P 0 = 0 := by norm_num [P]
  have hQzero : Q 0 = 0 := by norm_num [Q, P]
  have hFend : F (1 / 3) = Real.log 2 := by
    dsimp [F]
    norm_num only
    rw [show (4 / 3 : ℝ) = 2 * (2 / 3) by norm_num]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (2 / 3 : ℝ) ≠ 0)]
    ring
  have hLower : P (1 / 3) < Real.log 2 := by
    dsimp [Dlow] at hLowInc
    rw [hFzero, hPzero, hFend] at hLowInc
    linarith
  have hUpper : Real.log 2 < Q (1 / 3) := by
    dsimp [Dup] at hUpInc
    rw [hQzero, hFzero, hFend] at hUpInc
    linarith
  constructor
  · have hnum : (0.69314 : ℝ) < P (1 / 3) := by
      norm_num [P]
    exact hnum.trans hLower
  · have hnum : Q (1 / 3) < (0.69316 : ℝ) := by
      norm_num [Q, P]
    exact hUpper.trans hnum

private theorem remainder_abs_bounds :
    (1 / 3072 : ℝ) < |remainder| ∧ |remainder| < 1 / 384 := by
  have ht : trapezoidApprox = (200107 / 288288 : ℝ) := by
    rw [trapezoidApprox, interiorSum_exact]
    norm_num [sample, mesh]
  rw [remainder, exactIntegral_eq_log_two, ht]
  have hn : Real.log 2 - (200107 / 288288 : ℝ) < 0 := by
    nlinarith [log_two_decimal_bounds.2]
  rw [abs_of_neg hn]
  constructor <;> nlinarith [log_two_decimal_bounds.1, log_two_decimal_bounds.2]

private theorem trapezoid_remainder_exists :
    ∃ ξ ∈ Set.Ioo (0 : ℝ) 1,
      |remainder| =
        |(1 / (12 * 8 ^ 2) : ℝ) * (2 / (1 + ξ) ^ 3)| := by
  let g : ℝ → ℝ := fun x => 1 / (384 * (2 - x) ^ 3)
  have hg : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.div continuousOn_const
      (continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow 3))
    intro x hx
    dsimp
    have hne : 2 - x ≠ 0 := by linarith [hx.2]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hne)
  have hg0 : g 0 = (1 / 3072 : ℝ) := by
    norm_num [g]
  have hg1 : g 1 = (1 / 384 : ℝ) := by
    norm_num [g]
  have hy : |remainder| ∈ Set.Icc (g 0) (g 1) := by
    rw [hg0, hg1]
    exact ⟨le_of_lt remainder_abs_bounds.1,
      le_of_lt remainder_abs_bounds.2⟩
  obtain ⟨x, hx, hxeq⟩ :=
    intermediate_value_Icc (f := g) (by norm_num : (0 : ℝ) ≤ 1) hg hy
  have hxne0 : x ≠ 0 := by
    intro h
    have heq : g x = (1 / 3072 : ℝ) := by
      rw [h]
      norm_num [g]
    have hrem : |remainder| = (1 / 3072 : ℝ) := hxeq.symm.trans heq
    linarith [remainder_abs_bounds.1]
  have hxne1 : x ≠ 1 := by
    intro h
    have heq : g x = (1 / 384 : ℝ) := by
      rw [h]
      norm_num [g]
    have hrem : |remainder| = (1 / 384 : ℝ) := hxeq.symm.trans heq
    linarith [remainder_abs_bounds.2]
  have hx0 : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxne0)
  have hx1 : x < 1 := lt_of_le_of_ne hx.2 hxne1
  refine ⟨1 - x, ⟨by linarith, by linarith⟩, ?_⟩
  have hbase : 0 < 1 + (1 - x) := by linarith
  have hp :
      0 < (1 / (12 * 8 ^ 2) : ℝ) * (2 / (1 + (1 - x)) ^ 3) := by
    apply mul_pos
    · norm_num
    · exact div_pos (by norm_num) (pow_pos hbase 3)
  calc
    |remainder| = g x := hxeq.symm
    _ = |(1 / (12 * 8 ^ 2) : ℝ) * (2 / (1 + (1 - x)) ^ 3)| := by
      rw [abs_of_pos hp]
      dsimp [g]
      rw [show 1 + (1 - x) = 2 - x by ring]
      have htwoPos : 0 < 2 - x := by linarith [hx1]
      have hpow : (2 - x) ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt htwoPos)
      have hleft : (384 * (2 - x) ^ 3 : ℝ) ≠ 0 :=
        mul_ne_zero (by norm_num) hpow
      have hconst : (12 * 8 ^ 2 : ℝ) ≠ 0 := by norm_num
      field_simp [hleft, hconst, hpow] <;> ring

theorem gap1 (h : ℝ) (hh : h = 1 / 8) : h = 1 / 8 := by
  exact hh
theorem gap2 : (1 / 8 : ℝ) = 0.125 := by
  norm_num
theorem gap3 (h : ℝ) (hh : h = 1 / 8) : h = 0.125 := by
  calc
    h = 1 / 8 := hh
    _ = 0.125 := gap2
theorem gap4 : mesh 0 = 0 := by
  norm_num [mesh]
theorem gap5 : sample 0 = 1 := by
  norm_num [sample, mesh]
theorem gap6 : mesh 1 = 1 / 8 := by
  norm_num [mesh]
theorem gap7 : (1 / 8 : ℝ) = 0.125 := by
  exact gap2
theorem gap8 : mesh 1 = 0.125 := by
  rw [gap6, gap7]
theorem gap9 : sample 1 = 8 / 9 := by
  norm_num [sample, mesh]
theorem gap10 : mesh 2 = 0.25 := by
  norm_num [mesh]
theorem gap11 : sample 2 = 0.8 := by
  norm_num [sample, mesh]
theorem gap12 : mesh 3 = 0.375 := by
  norm_num [mesh]
theorem gap13 : sample 3 = 8 / 11 := by
  norm_num [sample, mesh]
theorem gap14 : mesh 4 = 0.5 := by
  norm_num [mesh]
theorem gap15 : sample 4 = 2 / 3 := by
  norm_num [sample, mesh]
theorem gap16 : mesh 5 = 0.625 := by
  norm_num [mesh]
theorem gap17 : sample 5 = 8 / 13 := by
  norm_num [sample, mesh]
theorem gap18 : mesh 6 = 0.75 := by
  norm_num [mesh]
theorem gap19 : sample 6 = 4 / 7 := by
  norm_num [sample, mesh]
theorem gap20 : mesh 7 = 0.875 := by
  norm_num [mesh]
theorem gap21 : sample 7 = 8 / 15 := by
  norm_num [sample, mesh]
theorem gap22 : mesh 8 = 1 := by
  norm_num [mesh]
theorem gap23 : sample 8 = 0.5 := by
  norm_num [sample, mesh]

theorem gap24 :
    (sample 0 + sample 8) / 2 = (1 + 0.5) / 2 := by
  rw [gap5, gap23]

theorem gap25 : ((1 + 0.5) / 2 : ℝ) = 0.75 := by
  norm_num

theorem gap26 : (sample 0 + sample 8) / 2 = 0.75 := by
  calc
    (sample 0 + sample 8) / 2 = (1 + 0.5) / 2 := gap24
    _ = 0.75 := gap25

theorem gap27 :
    interiorSum =
      8 / 9 + 4 / 5 + 8 / 11 + 2 / 3 + 8 / 13 + 4 / 7 + 8 / 15 := by
  exact interiorSum_exact

theorem gap28 :
    |(0.88889 + 0.8 + 0.72727 + 0.66667 + 0.61538 +
      0.57143 + 0.53333 : ℝ) - 4.80297| = 0 := by
  norm_num

theorem gap29 :
    interiorSum =
      8 / 9 + 4 / 5 + 8 / 11 + 2 / 3 + 8 / 13 + 4 / 7 + 8 / 15 := by
  exact gap27

theorem gap30 :
    |exactIntegral - trapezoidApprox| ≤ 1 / 384 := by
  simpa [remainder] using le_of_lt remainder_abs_bounds.2

theorem gap31 :
    trapezoidApprox =
      (1 / 8 : ℝ) *
        (0.75 + (8 / 9 + 4 / 5 + 8 / 11 + 2 / 3 +
          8 / 13 + 4 / 7 + 8 / 15)) := by
  rw [trapezoidApprox, gap26, gap29]

theorem gap32 :
    |trapezoidApprox - 0.69412| < 0.00001 := by
  rw [gap31]
  norm_num [abs_lt]

theorem gap33 :
    |exactIntegral - 0.69412| < 0.0027 := by
  calc
    |exactIntegral - 0.69412| =
        |(exactIntegral - trapezoidApprox) + (trapezoidApprox - 0.69412)| := by
          congr 1
          ring
    _ ≤ |exactIntegral - trapezoidApprox| + |trapezoidApprox - 0.69412| := abs_add_le _ _
    _ < 1 / 384 + 0.00001 := add_lt_add_of_le_of_lt gap30 gap32
    _ < 0.0027 := by norm_num

theorem gap34 :
    ∃ ξ ∈ Set.Ioo (0 : ℝ) 1,
      |remainder| =
        |(1 / (12 * 8 ^ 2) : ℝ) * (2 / (1 + ξ) ^ 3)| := by
  exact trapezoid_remainder_exists

theorem gap35 : |remainder| ≤ 2 / (12 * 8 ^ 2) := by
  have h := le_of_lt remainder_abs_bounds.2
  norm_num at h ⊢
  exact h

theorem gap36 : (2 / (12 * 8 ^ 2) : ℝ) < 0.0027 := by
  norm_num

theorem gap37 : (0.0027 : ℝ) = 2.7 * 10 ^ (-3 : ℤ) := by
  norm_num [zpow_neg]

theorem gap38 : |remainder| < 2.7 * 10 ^ (-3 : ℤ) := by
  calc
    |remainder| ≤ 2 / (12 * 8 ^ 2) := gap35
    _ < 0.0027 := gap36
    _ = 2.7 * 10 ^ (-3 : ℤ) := gap37

theorem gap39 :
    exactIntegral = Real.log (1 + 1) - Real.log (1 + 0) := by
  calc
    exactIntegral = Real.log 2 := exactIntegral_eq_log_two
    _ = Real.log (1 + 1) - Real.log (1 + 0) := by norm_num

theorem gap40 :
    Real.log (1 + 1) - Real.log (1 + 0) = Real.log 2 := by
  norm_num

theorem gap41 : |Real.log 2 - 0.69315| < 0.00001 := by
  rw [abs_lt]
  constructor <;> nlinarith [log_two_decimal_bounds.1, log_two_decimal_bounds.2]

theorem gap42 : |exactIntegral - 0.69315| < 0.00001 := by
  rw [gap39, gap40]
  exact gap41

end

end ProofGap.Exercise2532
