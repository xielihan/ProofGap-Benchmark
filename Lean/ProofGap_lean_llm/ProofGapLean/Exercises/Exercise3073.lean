import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3073

noncomputable section

open Filter
open scoped BigOperators Topology

def ratio (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) / ((n : ℝ) + 2)

def rootTerm (n : ℕ) : ℝ :=
  Real.sqrt (ratio n)

def logRatioTerm (n : ℕ) : ℝ :=
  Real.log (1 - 1 / ((n : ℝ) + 2))

def logPartialSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), logRatioTerm i

def partialProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range (n + 1), rootTerm i

def NonzeroConvergentProduct : Prop :=
  ∃ P : ℝ, P ≠ 0 ∧ Tendsto partialProduct atTop (𝓝 P)

def DivergentProduct : Prop :=
  ¬NonzeroConvergentProduct

/-- Source: `proof_gap/exercise_3073/1.txt`; retain the definition of arbitrary `p`. -/
private lemma logRangeSum_eq (n : ℕ) :
    (∑ i ∈ Finset.range n, logRatioTerm i) =
      -Real.log ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      unfold logRatioTerm
      have hden : (n : ℝ) + 2 ≠ 0 := by positivity
      have hnum : (n : ℝ) + 1 ≠ 0 := by positivity
      have hid :
          1 - 1 / ((n : ℝ) + 2) =
            ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
        field_simp [hden]
        <;> ring
      rw [hid, Real.log_div hnum hden]
      simp only [Nat.cast_succ]
      ring

theorem gap1 (p : ℕ → ℝ) (hp : ∀ n, p n = rootTerm n) :
    ∀ n, Real.log (p n) = (1 / 2 : ℝ) * Real.log (ratio n) := by
  intro n
  rw [hp n]
  unfold rootTerm
  have hr : 0 < ratio n := by
    unfold ratio
    positivity
  have hs : Real.sqrt (ratio n) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hr)
  have hsq : Real.sqrt (ratio n) * Real.sqrt (ratio n) = ratio n := by
    simpa [pow_two] using Real.sq_sqrt (le_of_lt hr)
  calc
    Real.log (Real.sqrt (ratio n)) =
        (1 / 2 : ℝ) *
          (Real.log (Real.sqrt (ratio n)) + Real.log (Real.sqrt (ratio n))) := by
            ring
    _ = (1 / 2 : ℝ) *
          Real.log (Real.sqrt (ratio n) * Real.sqrt (ratio n)) := by
            rw [Real.log_mul hs hs]
    _ = (1 / 2 : ℝ) * Real.log (ratio n) := by rw [hsq]

/-- Source: `proof_gap/exercise_3073/2.txt`. -/
theorem gap2 :
    ∀ n,
      (1 / 2 : ℝ) * Real.log (ratio n) =
        (1 / 2 : ℝ) * logRatioTerm n := by
  intro n
  have hden : (n : ℝ) + 2 ≠ 0 := by positivity
  have hid :
      ((n : ℝ) + 1) / ((n : ℝ) + 2) =
        1 - 1 / ((n : ℝ) + 2) := by
    field_simp [hden]
    <;> ring
  unfold ratio logRatioTerm
  rw [hid]

/-- Source: `proof_gap/exercise_3073/3.txt`; retain the definition of arbitrary `p`. -/
theorem gap3 (p : ℕ → ℝ) (hp : ∀ n, p n = rootTerm n) :
    ∀ n, Real.log (p n) = (1 / 2 : ℝ) * logRatioTerm n := by
  intro n
  rw [gap1 p hp n, gap2 n]

/-- Source: `proof_gap/exercise_3073/4.txt`. -/
theorem gap4 : ¬Summable logRatioTerm := by
  intro hsum
  have harg :
      Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    obtain ⟨N : ℕ, hN⟩ := exists_nat_ge b
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlog :
      Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  have hbot :
      Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, logRatioTerm i)
        atTop atBot := by
    refine tendsto_atBot.2 ?_
    intro b
    filter_upwards [(tendsto_atTop.1 hlog (-b))] with n hn
    rw [logRangeSum_eq]
    linarith
  have hnhds :
      Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, logRatioTerm i)
        atTop (𝓝 (∑' i, logRatioTerm i)) :=
    hsum.hasSum.tendsto_sum_nat
  have hgt :
      ∀ᶠ n in atTop,
        (∑' i, logRatioTerm i) - 1 <
          ∑ i ∈ Finset.range n, logRatioTerm i :=
    (tendsto_order.1 hnhds).1 _ (by linarith)
  have hle :
      ∀ᶠ n in atTop,
        (∑ i ∈ Finset.range n, logRatioTerm i) ≤
          (∑' i, logRatioTerm i) - 1 :=
    tendsto_atBot.1 hbot _
  rcases (hgt.and hle).exists with ⟨n, hn_gt, hn_le⟩
  exact (not_lt_of_ge hn_le) hn_gt

/-- Source: `proof_gap/exercise_3073/5.txt`; express divergence to `-∞` by a filter limit. -/
theorem gap5 : Tendsto logPartialSum atTop atBot := by
  have hpartial :
      ∀ n : ℕ, logPartialSum n = -Real.log ((n : ℝ) + 2) := by
    intro n
    have hcast :
        (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    unfold logPartialSum
    rw [logRangeSum_eq, hcast]
  have harg :
      Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    obtain ⟨N : ℕ, hN⟩ := exists_nat_ge b
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlog :
      Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  refine tendsto_atBot.2 ?_
  intro b
  filter_upwards [(tendsto_atTop.1 hlog (-b))] with n hn
  rw [hpartial n]
  linarith

/--
Source: `proof_gap/exercise_3073/6.txt`; divergence means failure to converge
to a nonzero product value.
-/
theorem gap6 : DivergentProduct := by
  intro hconv
  obtain ⟨P, hP, hPconv⟩ := hconv
  have hprodlog :
      ∀ m : ℕ,
        Real.log (∏ i ∈ Finset.range m, rootTerm i) =
          (1 / 2 : ℝ) *
            ∑ i ∈ Finset.range m, logRatioTerm i := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>
        have hrootpos : 0 < rootTerm m := by
          unfold rootTerm ratio
          positivity
        have hprodpos :
            0 < ∏ i ∈ Finset.range m, rootTerm i := by
          apply Finset.prod_pos
          intro i hi
          unfold rootTerm ratio
          positivity
        have hrootlog :
            Real.log (rootTerm m) =
              (1 / 2 : ℝ) * logRatioTerm m :=
          gap3 rootTerm (fun _ => rfl) m
        rw [Finset.prod_range_succ, Finset.sum_range_succ]
        rw [Real.log_mul (ne_of_gt hprodpos) (ne_of_gt hrootpos)]
        rw [ihm, hrootlog]
        ring
  have hlogprod :
      ∀ n : ℕ,
        Real.log (partialProduct n) =
          (1 / 2 : ℝ) * logPartialSum n := by
    intro n
    change
      Real.log (∏ i ∈ Finset.range (n + 1), rootTerm i) =
        (1 / 2 : ℝ) *
          ∑ i ∈ Finset.range (n + 1), logRatioTerm i
    exact hprodlog (n + 1)
  have hscaled :
      Tendsto
        (fun n : ℕ => (1 / 2 : ℝ) * logPartialSum n)
        atTop atBot := by
    refine tendsto_atBot.2 ?_
    intro b
    filter_upwards [(tendsto_atBot.1 gap5 (2 * b))] with n hn
    linarith
  have hlogbot :
      Tendsto (fun n : ℕ => Real.log (partialProduct n)) atTop atBot := by
    simpa only [hlogprod] using hscaled
  have hlognhds :
      Tendsto
        (fun n : ℕ => Real.log (partialProduct n))
        atTop (𝓝 (Real.log P)) :=
    (Real.continuousAt_log hP).tendsto.comp hPconv
  have hgt :
      ∀ᶠ n in atTop,
        Real.log P - 1 < Real.log (partialProduct n) :=
    (tendsto_order.1 hlognhds).1 _ (by linarith)
  have hle :
      ∀ᶠ n in atTop,
        Real.log (partialProduct n) ≤ Real.log P - 1 :=
    tendsto_atBot.1 hlogbot _
  rcases (hgt.and hle).exists with ⟨n, hn_gt, hn_le⟩
  exact (not_lt_of_ge hn_le) hn_gt

end

end ProofGap.Exercise3073
