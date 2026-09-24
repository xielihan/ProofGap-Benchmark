import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed

namespace ProofGap.Exercise2922

noncomputable section

open scoped BigOperators

def Approx (x y ε : ℝ) : Prop :=
  |x - y| < ε

def arctanTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (2 * n + 1) / (2 * n + 1 : ℕ)

def arctanRemainder (degree : ℕ) : ℝ :=
  Real.arctan (1 / 11 : ℝ) -
    ∑ n ∈ Finset.range ((degree + 1) / 2),
      arctanTerm (1 / 11 : ℝ) n

def nthRoot (n : ℕ) (x : ℝ) : ℝ :=
  Real.rpow x (1 / (n : ℝ))

def generalizedBinomial (a : ℝ) (n : ℕ) : ℝ :=
  (∏ k ∈ Finset.range n, (a - (k : ℝ))) /
    (Nat.factorial n : ℝ)

def rootPerturbation : ℝ :=
  3 / 128

def rootBinomialTerm (n : ℕ) : ℝ :=
  generalizedBinomial (1 / 10 : ℝ) n *
    (-rootPerturbation) ^ n

def rootPartial (m : ℕ) : ℝ :=
  2 * ∑ n ∈ Finset.range m, rootBinomialTerm n

def rootRemainder (m : ℕ) : ℝ :=
  nthRoot 10 1000 - rootPartial m

def rootRemainderBound : ℝ :=
  2 *
    (((1 / 10 : ℝ) * ((1 / 10 : ℝ) - 1) *
      ((1 / 10 : ℝ) - 2)) / (Nat.factorial 3 : ℝ)) *
    rootPerturbation ^ 3 *
    ∑' n : ℕ, rootPerturbation ^ n

def expTerm (n : ℕ) : ℝ :=
  (-1 / 2 : ℝ) ^ n / (Nat.factorial n : ℝ)

def expRemainder (m : ℕ) : ℝ :=
  Real.exp (-1 / 2 : ℝ) -
    ∑ n ∈ Finset.range m, expTerm n

def logTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (1 / 4 : ℝ) ^ (n + 1) / (n + 1 : ℕ)

def logRemainder (m : ℕ) : ℝ :=
  Real.log (1 + (1 / 4 : ℝ)) -
    ∑ n ∈ Finset.range m, logTerm n

private theorem arctan_hasSum :
    HasSum (arctanTerm (1 / 11 : ℝ))
      (Real.arctan (1 / 11 : ℝ)) := by
  have hs :=
    Real.hasSum_arctan
      (x := (1 / 11 : ℝ)) (by norm_num [Real.norm_eq_abs])
  apply hs.congr_fun
  intro n
  unfold arctanTerm
  push_cast
  ring

private def arctanMagnitude (n : ℕ) : ℝ :=
  (1 / 11 : ℝ) ^ (2 * n + 1) / (2 * n + 1 : ℕ)

private theorem arctanMagnitude_summable :
    Summable arctanMagnitude := by
  have hgeo :
      Summable (fun n : ℕ => (1 / 121 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs])
  have hmajor :
      Summable (fun n : ℕ => (1 / 11 : ℝ) ^ (2 * n + 1)) := by
    apply (hgeo.mul_left (1 / 11 : ℝ)).congr
    intro n
    rw [show 2 * n + 1 = 1 + 2 * n by omega, pow_add, pow_mul]
    norm_num
  apply Summable.of_nonneg_of_le
  · intro n
    unfold arctanMagnitude
    positivity
  · intro n
    unfold arctanMagnitude
    apply div_le_self
    · positivity
    · push_cast
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
  · exact hmajor

private theorem arctanMagnitude_antitone :
    Antitone arctanMagnitude := by
  apply antitone_nat_of_succ_le
  intro n
  unfold arctanMagnitude
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add]
  push_cast
  norm_num
  have hprod :
      0 ≤ (1 / 11 : ℝ) ^ (2 * n + 1) * (2 * (n : ℝ) + 1) := by
    positivity
  nlinarith

private theorem arctan_partial_tendsto :
    Filter.Tendsto
      (fun n => ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * arctanMagnitude i)
      Filter.atTop (nhds (Real.arctan (1 / 11 : ℝ))) := by
  have heq :
      (fun n => ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * arctanMagnitude i) =
      fun n => ∑ i ∈ Finset.range n, arctanTerm (1 / 11 : ℝ) i := by
    funext n
    apply Finset.sum_congr rfl
    intro i hi
    unfold arctanMagnitude arctanTerm
    push_cast
    ring
  rw [heq]
  exact arctan_hasSum.tendsto_sum_nat

private theorem nthRoot_pow_eq
    (n : ℕ) (a : ℝ) (hn : 0 < n) (ha : 0 < a) :
    nthRoot n (a ^ n) = a := by
  unfold nthRoot
  simpa [one_div] using
    (Real.pow_rpow_inv_natCast (x := a) (n := n)
      (le_of_lt ha) (ne_of_gt hn))

private theorem rootPartial_three :
    rootPartial 3 = (3269039 / 1638400 : ℝ) := by
  norm_num [rootPartial, rootBinomialTerm, generalizedBinomial,
    rootPerturbation, Finset.sum_range_succ, Finset.prod_range_succ,
    Nat.factorial]

private theorem tsum_rootPerturbation :
    (∑' n : ℕ, rootPerturbation ^ n) = (128 / 125 : ℝ) := by
  calc
    (∑' n : ℕ, rootPerturbation ^ n) =
        (1 - rootPerturbation)⁻¹ := by
      exact tsum_geometric_of_norm_lt_one
        (by norm_num [rootPerturbation, Real.norm_eq_abs])
    _ = (128 / 125 : ℝ) := by
      norm_num [rootPerturbation]

private theorem rootRemainderBound_value :
    rootRemainderBound = (1539 / 2048000000 : ℝ) := by
  rw [rootRemainderBound, tsum_rootPerturbation]
  norm_num [rootPerturbation, Nat.factorial]

private theorem root_error_bound :
    |rootRemainder 3| < rootRemainderBound := by
  rw [rootRemainder, abs_lt]
  let l : ℝ := rootPartial 3 - rootRemainderBound
  let u : ℝ := rootPartial 3 + rootRemainderBound
  have hlpow : l ^ 10 < (1000 : ℝ) := by
    dsimp [l]
    rw [rootPartial_three, rootRemainderBound_value]
    norm_num
  have hupow : (1000 : ℝ) < u ^ 10 := by
    dsimp [u]
    rw [rootPartial_three, rootRemainderBound_value]
    norm_num
  have hl : l < nthRoot 10 1000 := by
    calc
      l = nthRoot 10 (l ^ 10) :=
        (nthRoot_pow_eq 10 l (by norm_num)
          (by
            dsimp [l]
            rw [rootPartial_three, rootRemainderBound_value]
            norm_num)).symm
      _ < nthRoot 10 1000 := by
        unfold nthRoot
        exact Real.rpow_lt_rpow (by positivity) hlpow (by norm_num)
  have hu : nthRoot 10 1000 < u := by
    calc
      nthRoot 10 1000 < nthRoot 10 (u ^ 10) := by
        unfold nthRoot
        exact Real.rpow_lt_rpow (by positivity) hupow (by norm_num)
      _ = u :=
        nthRoot_pow_eq 10 u (by norm_num)
          (by
            dsimp [u]
            rw [rootPartial_three, rootRemainderBound_value]
            norm_num)
  dsimp [l] at hl
  dsimp [u] at hu
  constructor <;> linarith

private theorem exp_hasSum :
    HasSum expTerm (Real.exp (-1 / 2 : ℝ)) := by
  simpa [expTerm, Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp (-1 / 2 : ℝ))

private def expMagnitude (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n / (Nat.factorial n : ℝ)

private theorem expMagnitude_summable :
    Summable expMagnitude := by
  exact
    (NormedSpace.expSeries_div_hasSum_exp (1 / 2 : ℝ)).summable

private theorem expMagnitude_antitone :
    Antitone expMagnitude := by
  apply antitone_nat_of_succ_le
  intro n
  unfold expMagnitude
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  have hprod :
      0 ≤ (1 / 2 : ℝ) ^ n * (Nat.factorial n : ℝ) := by
    positivity
  nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]

private theorem exp_partial_tendsto :
    Filter.Tendsto
      (fun n => ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * expMagnitude i)
      Filter.atTop (nhds (Real.exp (-1 / 2 : ℝ))) := by
  have heq :
      (fun n => ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * expMagnitude i) =
      fun n => ∑ i ∈ Finset.range n, expTerm i := by
    funext n
    apply Finset.sum_congr rfl
    intro i hi
    unfold expMagnitude expTerm
    rw [show (-1 / 2 : ℝ) = (-1 : ℝ) * (1 / 2 : ℝ) by ring,
      mul_pow]
    ring
  rw [heq]
  exact exp_hasSum.tendsto_sum_nat

private theorem log_hasSum :
    HasSum logTerm (Real.log (1 + (1 / 4 : ℝ))) := by
  have hs :=
    (Real.hasSum_pow_div_log_of_abs_lt_one
      (x := -(1 / 4 : ℝ)) (by norm_num)).neg
  have hs' :
      HasSum logTerm (- -Real.log (1 - -(1 / 4 : ℝ))) := by
    apply hs.congr_fun
    intro n
    unfold logTerm
    push_cast
    conv_rhs => rw [neg_pow]
    rw [pow_succ, pow_succ]
    ring
  convert hs' using 1
  ring

private def logMagnitude (n : ℕ) : ℝ :=
  (1 / 4 : ℝ) ^ (n + 1) / (n + 1 : ℕ)

private theorem logMagnitude_summable :
    Summable logMagnitude := by
  have hgeo :
      Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs])
  have hmajor :
      Summable (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1)) := by
    apply (hgeo.mul_left (1 / 4 : ℝ)).congr
    intro n
    rw [pow_succ]
    ring
  apply Summable.of_nonneg_of_le
  · intro n
    unfold logMagnitude
    positivity
  · intro n
    unfold logMagnitude
    apply div_le_self
    · positivity
    · push_cast
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
  · exact hmajor

private theorem logMagnitude_antitone :
    Antitone logMagnitude := by
  apply antitone_nat_of_succ_le
  intro n
  unfold logMagnitude
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]
  push_cast
  norm_num
  have hprod :
      0 ≤ (1 / 4 : ℝ) ^ (n + 1) * ((n : ℝ) + 1) := by
    positivity
  nlinarith

private theorem log_partial_tendsto :
    Filter.Tendsto
      (fun n => ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * logMagnitude i)
      Filter.atTop (nhds (Real.log (1 + (1 / 4 : ℝ)))) := by
  have heq :
      (fun n => ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * logMagnitude i) =
      fun n => ∑ i ∈ Finset.range n, logTerm i := by
    funext n
    apply Finset.sum_congr rfl
    intro i hi
    unfold logMagnitude logTerm
    ring
  rw [heq]
  exact log_hasSum.tendsto_sum_nat

theorem gap1 :
    Real.arctan (12 / 10 : ℝ) =
      Real.arctan 1 + Real.arctan (1 / 11 : ℝ) := by
  have h :=
    Real.arctan_add (x := (1 : ℝ)) (y := (1 / 11 : ℝ)) (by norm_num)
  norm_num at h ⊢
  exact h.symm

theorem gap2 :
    Real.arctan 1 + Real.arctan (1 / 11 : ℝ) =
      Real.pi / 4 + ∑' n : ℕ, arctanTerm (1 / 11 : ℝ) n := by
  rw [Real.arctan_one, arctan_hasSum.tsum_eq]

theorem gap3 :
    Real.arctan (12 / 10 : ℝ) =
      Real.pi / 4 + ∑' n : ℕ, arctanTerm (1 / 11 : ℝ) n := by
  rw [gap1, gap2]

theorem gap4 :
    |arctanRemainder 3| <
      (1 / 5 : ℝ) * (1 / 11 : ℝ) ^ 5 := by
  have hlower :=
    arctanMagnitude_antitone.alternating_series_le_tendsto
      arctan_partial_tendsto 1
  have hupper :=
    arctanMagnitude_antitone.tendsto_le_alternating_series
      arctan_partial_tendsto 2
  norm_num [arctanMagnitude, Finset.sum_range_succ] at hlower hupper
  rw [arctanRemainder, abs_lt]
  norm_num [arctanTerm, Finset.sum_range_succ]
  constructor <;> linarith

theorem gap5 :
    (1 / 5 : ℝ) * (1 / 11 : ℝ) ^ 5 <
      (1 / 10 ^ 5 : ℝ) := by
  norm_num

theorem gap6 :
    |arctanRemainder 3| < (1 / 10 ^ 5 : ℝ) := by
  exact gap4.trans gap5

theorem gap7 :
    Approx (Real.arctan (12 / 10 : ℝ)) (87606 / 100000 : ℝ)
      (1 / 10 ^ 5 : ℝ) := by
  have hrem := gap4
  rw [arctanRemainder, abs_lt] at hrem
  norm_num [arctanTerm, Finset.sum_range_succ] at hrem
  unfold Approx
  rw [gap1, Real.arctan_one, abs_lt]
  constructor
  · linarith [Real.pi_gt_d20]
  · linarith [Real.pi_lt_d20]

theorem gap8 :
    nthRoot 10 1000 = nthRoot 10 (1024 - 24) := by
  norm_num

theorem gap9 :
    nthRoot 10 (1024 - 24) =
      2 * Real.rpow (1 - rootPerturbation) (1 / 10 : ℝ) := by
  unfold nthRoot rootPerturbation
  have h2 : Real.rpow ((2 : ℝ) ^ 10) (1 / 10 : ℝ) = 2 := by
    convert Real.pow_rpow_inv_natCast (x := (2 : ℝ)) (n := 10)
      (by norm_num) (by norm_num) using 1
    all_goals norm_num
  calc
    Real.rpow (1024 - 24) (1 / (10 : ℝ)) =
        Real.rpow
          ((2 : ℝ) ^ 10 * (1 - (3 / 128 : ℝ)))
          (1 / 10 : ℝ) := by norm_num
    _ = Real.rpow ((2 : ℝ) ^ 10) (1 / 10 : ℝ) *
        Real.rpow (1 - (3 / 128 : ℝ)) (1 / 10 : ℝ) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.mul_rpow (by positivity) (by norm_num)]
    _ = 2 * Real.rpow (1 - (3 / 128 : ℝ)) (1 / 10 : ℝ) := by
      rw [h2]

theorem gap10 :
    nthRoot 10 1000 =
      2 * Real.rpow (1 - rootPerturbation) (1 / 10 : ℝ) := by
  rw [gap8, gap9]

theorem gap11 :
    Approx (nthRoot 10 1000) (rootPartial 3) rootRemainderBound := by
  simpa [Approx, rootRemainder] using root_error_bound

theorem gap12 :
    |rootRemainder 3| < rootRemainderBound := by
  exact root_error_bound

theorem gap13 :
    rootRemainderBound < (1 / 10 ^ 6 : ℝ) := by
  rw [rootRemainderBound_value]
  norm_num

theorem gap14 :
    |rootRemainder 3| < (1 / 10 ^ 6 : ℝ) := by
  exact root_error_bound.trans gap13

theorem gap15 :
    Approx (nthRoot 10 1000) (1995263 / 1000000 : ℝ)
      (1 / 10 ^ 6 : ℝ) := by
  unfold Approx
  calc
    |nthRoot 10 1000 - (1995263 / 1000000 : ℝ)| =
        |(nthRoot 10 1000 - rootPartial 3) +
          (rootPartial 3 - (1995263 / 1000000 : ℝ))| := by
      congr 1
      ring
    _ ≤ |nthRoot 10 1000 - rootPartial 3| +
          |rootPartial 3 - (1995263 / 1000000 : ℝ)| :=
      abs_add_le _ _
    _ < rootRemainderBound +
          |rootPartial 3 - (1995263 / 1000000 : ℝ)| := by
      simpa [rootRemainder] using
        add_lt_add_right root_error_bound
          |rootPartial 3 - (1995263 / 1000000 : ℝ)|
    _ < (1 / 10 ^ 6 : ℝ) := by
      rw [rootRemainderBound_value, rootPartial_three]
      norm_num

theorem gap16 :
    1 / nthRoot 2 (Real.exp 1) =
      Real.exp (-1 / 2 : ℝ) := by
  unfold nthRoot
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_def_of_pos (Real.exp_pos 1), Real.log_exp]
  convert (Real.exp_neg (1 / 2 : ℝ)).symm using 1 <;> ring

theorem gap17 :
    Real.exp (-1 / 2 : ℝ) =
      ∑' n : ℕ, expTerm n := by
  exact exp_hasSum.tsum_eq.symm

theorem gap18 :
    1 / nthRoot 2 (Real.exp 1) =
      ∑' n : ℕ, expTerm n := by
  rw [gap16, gap17]

theorem gap19 :
    |expRemainder 7| <
      1 / ((Nat.factorial 7 : ℝ) * 2 ^ 7) := by
  have hupper :=
    expMagnitude_antitone.tendsto_le_alternating_series
      exp_partial_tendsto 3
  have hlower :=
    expMagnitude_antitone.alternating_series_le_tendsto
      exp_partial_tendsto 5
  norm_num [expMagnitude, Finset.sum_range_succ, Nat.factorial] at hupper hlower
  rw [expRemainder, abs_lt]
  norm_num [expTerm, Finset.sum_range_succ, Nat.factorial]
  constructor <;> linarith

theorem gap20 :
    (1 / ((Nat.factorial 7 : ℝ) * 2 ^ 7)) <
      (1 / 10 ^ 5 : ℝ) := by
  norm_num [Nat.factorial]

theorem gap21 :
    |expRemainder 7| < (1 / 10 ^ 5 : ℝ) := by
  exact gap19.trans gap20

theorem gap22 :
    Approx (1 / nthRoot 2 (Real.exp 1)) (60653 / 100000 : ℝ)
      (1 / 10 ^ 5 : ℝ) := by
  have hrem := gap19
  rw [expRemainder, abs_lt] at hrem
  norm_num [expTerm, Finset.sum_range_succ, Nat.factorial] at hrem
  unfold Approx
  rw [gap16, abs_lt]
  constructor <;> linarith

theorem gap23 :
    Real.log (125 / 100 : ℝ) =
      Real.log (1 + (1 / 4 : ℝ)) := by
  congr 1
  norm_num

theorem gap24 :
    Real.log (1 + (1 / 4 : ℝ)) =
      ∑' n : ℕ, logTerm n := by
  exact log_hasSum.tsum_eq.symm

theorem gap25 :
    Real.log (125 / 100 : ℝ) =
      ∑' n : ℕ, logTerm n := by
  rw [gap23, gap24]

theorem gap26 :
    |logRemainder 6| < (1 / (7 * 4 ^ 7) : ℝ) := by
  have hlower :=
    logMagnitude_antitone.alternating_series_le_tendsto
      log_partial_tendsto 3
  have hupper :=
    logMagnitude_antitone.tendsto_le_alternating_series
      log_partial_tendsto 4
  norm_num [logMagnitude, Finset.sum_range_succ] at hlower hupper
  rw [logRemainder, abs_lt]
  norm_num [logTerm, Finset.sum_range_succ]
  constructor <;> linarith

theorem gap27 :
    (1 / (7 * 4 ^ 7) : ℝ) < (1 / 10 ^ 5 : ℝ) := by
  norm_num

theorem gap28 :
    |logRemainder 6| < (1 / 10 ^ 5 : ℝ) := by
  exact gap26.trans gap27

theorem gap29 :
    Approx (Real.log (125 / 100 : ℝ)) (22314 / 100000 : ℝ)
      (1 / 10 ^ 5 : ℝ) := by
  have hlower :=
    logMagnitude_antitone.alternating_series_le_tendsto
      log_partial_tendsto 3
  have hupper :=
    logMagnitude_antitone.tendsto_le_alternating_series
      log_partial_tendsto 4
  norm_num [logMagnitude, Finset.sum_range_succ] at hlower hupper
  unfold Approx
  rw [gap23, abs_lt]
  constructor <;> linarith

end

end ProofGap.Exercise2922
