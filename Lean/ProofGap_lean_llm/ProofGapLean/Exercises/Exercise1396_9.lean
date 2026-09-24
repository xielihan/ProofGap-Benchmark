import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace ProofGap.Exercise1396_9

noncomputable section

def Approx (x y ε : ℝ) : Prop := |x - y| < ε
def logPartial (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ (k + 1) * x ^ k / k
def y : ℝ := 1.2 * 0.0953
def expCubic (z : ℝ) : ℝ :=
  1 + z + z ^ 2 / 2 + z ^ 3 / (Nat.factorial 3 : ℝ)
def expRemainder : ℝ := |Real.exp y - expCubic y|

private theorem log_fifth_order_error :
    |Real.log (1 + (1 / 10 : ℝ)) -
        ((1 / 10 : ℝ) - (1 / 10 : ℝ) ^ 2 / 2 +
          (1 / 10 : ℝ) ^ 3 / 3 - (1 / 10 : ℝ) ^ 4 / 4 +
          (1 / 10 : ℝ) ^ 5 / 5)| <
      (1 / 10 : ℝ) ^ 6 / 6 := by
  let p : ℝ → ℝ := fun x =>
    x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 + x ^ 5 / 5
  let e : ℝ → ℝ := fun x => Real.log (1 + x) - p x
  have he (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) (1 / 10 : ℝ)) :
      HasDerivAt e (-x ^ 5 / (1 + x)) x := by
    have hlog :
        HasDerivAt (fun z : ℝ => Real.log (1 + z)) (1 + x)⁻¹ x := by
      simpa using
        (Real.hasDerivAt_log (by linarith [hx.1] : 1 + x ≠ 0)).comp x
          ((hasDerivAt_const x 1).add (hasDerivAt_id x))
    have h1 := hasDerivAt_id x
    have h2 := ((hasDerivAt_id x).pow 2).div_const 2
    have h3 := ((hasDerivAt_id x).pow 3).div_const 3
    have h4 := ((hasDerivAt_id x).pow 4).div_const 4
    have h5 := ((hasDerivAt_id x).pow 5).div_const 5
    have hp :
        HasDerivAt p (1 - x + x ^ 2 - x ^ 3 + x ^ 4) x := by
      dsimp [p]
      convert (((h1.sub h2).add h3).sub h4).add h5 using 1 <;>
        simp only [id_eq] <;> ring
    change HasDerivAt (fun z : ℝ => Real.log (1 + z) - p z)
      (-x ^ 5 / (1 + x)) x
    convert hlog.sub hp using 1
    field_simp [show 1 + x ≠ 0 by linarith [hx.1]]
    ring
  have hne (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) (1 / 10 : ℝ)) :
      HasDerivAt (fun z => -e z) (x ^ 5 / (1 + x)) x := by
    convert (he x hx).neg using 1
    ring
  have hh (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) (1 / 10 : ℝ)) :
      HasDerivAt (fun z => e z + z ^ 6 / 6) (x ^ 6 / (1 + x)) x := by
    convert (he x hx).add (((hasDerivAt_id x).pow 6).div_const 6) using 1
    simp only [id_eq]
    field_simp [show 1 + x ≠ 0 by linarith [hx.1]]
    ring
  have hzero : e 0 = 0 := by
    norm_num [e, p]
  have hneg : e (1 / 10 : ℝ) < 0 := by
    obtain ⟨c, hc, hcderiv⟩ :=
      exists_hasDerivAt_eq_slope
        (f := fun z : ℝ => -e z)
        (f' := fun x : ℝ => x ^ 5 / (1 + x))
        (by norm_num : (0 : ℝ) < 1 / 10)
        (by
          intro x hx
          exact (hne x hx).continuousAt.continuousWithinAt)
        (by
          intro x hx
          exact hne x ⟨hx.1.le, hx.2.le⟩)
    have hslope :
        ((-e (1 / 10 : ℝ) - (-e 0)) / ((1 / 10 : ℝ) - 0)) =
          c ^ 5 / (1 + c) :=
      hcderiv.symm
    have hcpos : 0 < c ^ 5 / (1 + c) :=
      div_pos (pow_pos hc.1 5) (by linarith [hc.1])
    have hslopepos :
        0 < ((-e (1 / 10 : ℝ) - (-e 0)) / ((1 / 10 : ℝ) - 0)) := by
      rw [hslope]
      exact hcpos
    rcases div_pos_iff.mp hslopepos with h | h
    · have hn := h.1
      rw [hzero] at hn
      linarith
    · norm_num at h
  have hpos : 0 < e (1 / 10 : ℝ) + (1 / 10 : ℝ) ^ 6 / 6 := by
    obtain ⟨c, hc, hcderiv⟩ :=
      exists_hasDerivAt_eq_slope
        (f := fun z : ℝ => e z + z ^ 6 / 6)
        (f' := fun x : ℝ => x ^ 6 / (1 + x))
        (by norm_num : (0 : ℝ) < 1 / 10)
        (by
          intro x hx
          exact (hh x hx).continuousAt.continuousWithinAt)
        (by
          intro x hx
          exact hh x ⟨hx.1.le, hx.2.le⟩)
    have hslope :
        ((e (1 / 10 : ℝ) + (1 / 10 : ℝ) ^ 6 / 6) -
            (e 0 + (0 : ℝ) ^ 6 / 6)) /
            ((1 / 10 : ℝ) - 0) =
          c ^ 6 / (1 + c) :=
      hcderiv.symm
    have hcpos : 0 < c ^ 6 / (1 + c) :=
      div_pos (pow_pos hc.1 6) (by linarith [hc.1])
    have hslopepos :
        0 <
          ((e (1 / 10 : ℝ) + (1 / 10 : ℝ) ^ 6 / 6) -
              (e 0 + (0 : ℝ) ^ 6 / 6)) /
            ((1 / 10 : ℝ) - 0) := by
      rw [hslope]
      exact hcpos
    rcases div_pos_iff.mp hslopepos with h | h
    · simpa [hzero] using h.1
    · norm_num at h
  change |e (1 / 10 : ℝ)| < (1 / 10 : ℝ) ^ 6 / 6
  rw [abs_lt]
  constructor
  · linarith
  · have hb : 0 < (1 / 10 : ℝ) ^ 6 / 6 := by positivity
    linarith

private theorem log_bounds :
    (571861 / 6000000 : ℝ) < Real.log 1.1 ∧
      Real.log 1.1 < (571863 / 6000000 : ℝ) := by
  have h := log_fifth_order_error
  rw [abs_lt] at h
  norm_num at h ⊢
  constructor <;> linarith [h.1, h.2]

private theorem exp_lower_numeric :
    (1.121169 : ℝ) < Real.exp (571861 / 5000000 : ℝ) := by
  have h :=
    Real.exp_bound (x := (571861 / 5000000 : ℝ)) (n := 6)
      (by norm_num : |(571861 / 5000000 : ℝ)| ≤ 1) (by norm_num)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith [h.1]

private theorem exp_upper_numeric :
    Real.exp (571863 / 5000000 : ℝ) < (1.121171 : ℝ) := by
  have h :=
    Real.exp_bound (x := (571863 / 5000000 : ℝ)) (n := 6)
      (by norm_num : |(571863 / 5000000 : ℝ)| ≤ 1) (by norm_num)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith [h.2]

private theorem expRemainder_lt :
    expRemainder < 7.9 * 10 ^ (-6 : ℤ) := by
  have h :=
    Real.exp_bound (x := y) (n := 5)
      (by norm_num [y] : |y| ≤ (1 : ℝ)) (by norm_num)
  unfold expRemainder
  calc
    |Real.exp y - expCubic y| ≤
        |Real.exp y -
            ∑ m ∈ Finset.range 5, y ^ m / (Nat.factorial m : ℝ)| +
          |(∑ m ∈ Finset.range 5, y ^ m / (Nat.factorial m : ℝ)) -
            expCubic y| := abs_sub_le _ _ _
    _ < 7.9 * 10 ^ (-6 : ℤ) := by
      norm_num [y, expCubic, Finset.sum_range_succ, Nat.factorial] at h ⊢
      linarith

theorem gap1 : Real.log 1.1 = Real.log (1 + 0.1) := by
  norm_num
theorem gap2 :
    Approx (Real.log (1 + 0.1)) (logPartial 0.1 5)
      (2 / 10000000 : ℝ) := by
  unfold Approx
  have hs :
      logPartial (1 / 10 : ℝ) 5 =
        (1 / 10 : ℝ) - (1 / 10 : ℝ) ^ 2 / 2 +
          (1 / 10 : ℝ) ^ 3 / 3 - (1 / 10 : ℝ) ^ 4 / 4 +
          (1 / 10 : ℝ) ^ 5 / 5 := by
    norm_num [logPartial, Finset.sum_Icc_succ_top]
  rw [show (0.1 : ℝ) = 1 / 10 by norm_num, hs]
  have h := log_fifth_order_error
  norm_num at h ⊢
  exact lt_trans h (by norm_num)
theorem gap3 :
    Approx (logPartial 0.1 5) 0.0953 (11 / 1000000 : ℝ) := by
  norm_num [Approx, logPartial, Finset.sum_Icc_succ_top]
theorem gap4 :
    Approx (Real.log 1.1) 0.0953 (11 / 1000000 : ℝ) := by
  rw [gap1]
  have h2 := gap2
  unfold Approx at h2 ⊢
  have hs :
      |logPartial 0.1 5 - 0.0953| = (31 / 3000000 : ℝ) := by
    norm_num [logPartial, Finset.sum_Icc_succ_top]
  calc
    |Real.log (1 + 0.1) - 0.0953| ≤
        |Real.log (1 + 0.1) - logPartial 0.1 5| +
          |logPartial 0.1 5 - 0.0953| := abs_sub_le _ _ _
    _ < (11 / 1000000 : ℝ) := by
      rw [hs]
      linarith
theorem gap5 : Real.rpow 1.1 1.2 = Real.exp (1.2 * Real.log 1.1) := by
  change (1.1 : ℝ) ^ (1.2 : ℝ) = Real.exp (1.2 * Real.log 1.1)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1.1)]
  congr 1
  ring
theorem gap6 :
    Approx (Real.exp (1.2 * Real.log 1.1)) (Real.exp y)
      (2 / 100000 : ℝ) := by
  unfold Approx
  let a : ℝ := 1.2 * Real.log 1.1
  let b : ℝ := y
  have hab : b < a := by
    dsimp [a, b, y]
    linarith [log_bounds.1]
  have hab_small : a - b < (63 / 5000000 : ℝ) := by
    dsimp [a, b, y]
    linarith [log_bounds.2]
  obtain ⟨c, hc, hcderiv⟩ :=
    exists_hasDerivAt_eq_slope
      (f := Real.exp)
      (f' := Real.exp)
      hab
      (by
        intro x hx
        exact (Real.hasDerivAt_exp x).continuousAt.continuousWithinAt)
      (by
        intro x hx
        exact Real.hasDerivAt_exp x)
  have hc_upper : c < (3 / 25 : ℝ) := by
    calc
      c < a := hc.2
      _ < (3 / 25 : ℝ) := by
        dsimp [a]
        linarith [log_bounds.2]
  have hc_nonneg : 0 ≤ c := by
    have hbpos : 0 < b := by norm_num [b, y]
    linarith [hc.1]
  have hexp_c : Real.exp c < (6 / 5 : ℝ) := by
    have hbound :=
      Real.exp_bound_div_one_sub_of_interval hc_nonneg
        (by linarith [hc_upper] : c < 1)
    have hden : 0 < 1 - c := by linarith [hc_upper]
    have hinv : 1 / (1 - c) < (6 / 5 : ℝ) := by
      rw [div_lt_iff₀ hden]
      linarith [hc_upper]
    exact lt_of_le_of_lt hbound hinv
  have hslope :
      (Real.exp a - Real.exp b) / (a - b) = Real.exp c :=
    hcderiv.symm
  have hexp_diff :
      Real.exp a - Real.exp b = Real.exp c * (a - b) := by
    field_simp [ne_of_gt (sub_pos.mpr hab)] at hslope
    linarith
  have hdiff_pos : 0 < Real.exp a - Real.exp b :=
    sub_pos.mpr (Real.exp_lt_exp.mpr hab)
  change |Real.exp a - Real.exp b| < 2 / 100000
  rw [abs_of_pos hdiff_pos, hexp_diff]
  have hacpos : 0 < a - b := sub_pos.mpr hab
  nlinarith [Real.exp_pos c]
theorem gap7 :
    Approx (Real.exp y) 1.12117 (2 / 100000 : ℝ) := by
  unfold Approx
  have h :=
    Real.exp_bound (x := y) (n := 5)
      (by norm_num [y] : |y| ≤ (1 : ℝ)) (by norm_num)
  calc
    |Real.exp y - 1.12117| ≤
        |Real.exp y -
            ∑ m ∈ Finset.range 5, y ^ m / (Nat.factorial m : ℝ)| +
          |(∑ m ∈ Finset.range 5, y ^ m / (Nat.factorial m : ℝ)) -
            1.12117| := abs_sub_le _ _ _
    _ < (2 / 100000 : ℝ) := by
      norm_num [y, Finset.sum_range_succ, Nat.factorial] at h ⊢
      linarith
theorem gap8 :
    Approx (Real.rpow 1.1 1.2) 1.12117 (1 / 1000000 : ℝ) := by
  rw [gap5]
  unfold Approx
  rw [abs_lt]
  have hlo :
      (571861 / 5000000 : ℝ) < 1.2 * Real.log 1.1 := by
    linarith [log_bounds.1]
  have hhi :
      1.2 * Real.log 1.1 < (571863 / 5000000 : ℝ) := by
    linarith [log_bounds.2]
  constructor
  · have he :=
      Real.exp_lt_exp.mpr hlo |>.trans' exp_lower_numeric
    norm_num at he ⊢
    linarith
  · have he :=
      (Real.exp_lt_exp.mpr hhi).trans exp_upper_numeric
    norm_num at he ⊢
    linarith
theorem gap9 :
    ∃ θ ∈ Set.Ioo (0 : ℝ) 1,
      expRemainder = Real.exp (θ * y) * y ^ 4 / (Nat.factorial 4 : ℝ) := by
  have hypos : 0 < y := by norm_num [y]
  have hf : ContDiffOn ℝ 4 Real.exp (Set.Icc 0 y) := by
    exact (Real.contDiff_exp : ContDiff ℝ 4 Real.exp).contDiffOn
  rcases taylor_mean_remainder_lagrange_iteratedDeriv hypos hf with
    ⟨c, hc, hrem⟩
  have hderiv (k : ℕ) :
      iteratedDerivWithin k Real.exp (Set.Icc 0 y) 0 = 1 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc hypos)
      (show ContDiffAt ℝ k Real.exp 0 by
        exact (Real.contDiff_exp : ContDiff ℝ k Real.exp).contDiffAt)
      ⟨le_rfl, hypos.le⟩]
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
    norm_num
  have heval :
      taylorWithinEval Real.exp 3 (Set.Icc 0 y) 0 y = expCubic y := by
    rw [taylor_within_apply]
    simp_rw [hderiv]
    unfold expCubic
    norm_num [Finset.sum_range_succ, Nat.factorial]
    ring
  refine ⟨c / y, ⟨div_pos hc.1 hypos,
    (div_lt_one hypos).2 hc.2⟩, ?_⟩
  rw [heval] at hrem
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp] at hrem
  unfold expRemainder
  rw [show c / y * y = c by field_simp]
  norm_num [Nat.factorial] at hrem ⊢
  rw [hrem]
  have hnonneg :
      0 ≤ Real.exp c * y ^ 4 / 24 := by positivity
  rw [abs_of_nonneg hnonneg]
theorem gap10 :
    ∃ θ ∈ Set.Ioo (0 : ℝ) 1,
      Real.exp (θ * y) * y ^ 4 / (Nat.factorial 4 : ℝ) <
        7.9 * 10 ^ (-6 : ℤ) := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  have hbound :=
    Real.exp_bound_div_one_sub_of_interval
      (x := (1 / 2 : ℝ) * y)
      (by norm_num [y])
      (by norm_num [y])
  norm_num [y, Nat.factorial] at hbound ⊢
  nlinarith [Real.exp_pos ((1 / 2 : ℝ) * y)]
theorem gap11 : ∃ Δ : ℝ, Δ = expRemainder ∧ Δ < 7.9 * 10 ^ (-6 : ℤ) := by
  exact ⟨expRemainder, rfl, expRemainder_lt⟩

end
end ProofGap.Exercise1396_9
