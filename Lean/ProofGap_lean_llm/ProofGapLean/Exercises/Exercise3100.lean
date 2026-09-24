import ProofGapLean.Prelude.Analysis
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.EulerProduct.Basic

namespace ProofGap.Exercise3100

noncomputable section

open Filter
open scoped BigOperators Topology

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

def reciprocalPower (x : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow (n : ℝ) x

def zetaSeries (x : ℝ) : ℝ :=
  ∑' k : ℕ, reciprocalPower x (k + 1)

def primesUpTo (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter Nat.Prime

def eulerFactor (x : ℝ) (p : ℕ) : ℝ :=
  (1 - reciprocalPower x p)⁻¹

def eulerPartialProduct (x : ℝ) (N : ℕ) : ℝ :=
  ∏ p ∈ primesUpTo N, eulerFactor x p

def IsSmoothUpTo (N n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ≤ N

def smoothSeries (x : ℝ) (N : ℕ) : ℝ :=
  ∑' k : ℕ,
    if IsSmoothUpTo N (k + 1) then reciprocalPower x (k + 1) else 0

def tailSeries (x : ℝ) (N : ℕ) : ℝ :=
  ∑' k : ℕ, reciprocalPower x (N + 1 + k)

private def reciprocalPowerHom (x : ℝ) : ℕ →* ℝ where
  toFun := reciprocalPower x
  map_one' := by simp [reciprocalPower]
  map_mul' m n := by
    unfold reciprocalPower
    push_cast
    change 1 / (((m : ℝ) * (n : ℝ)) ^ x) =
      1 / ((m : ℝ) ^ x) * (1 / ((n : ℝ) ^ x))
    rw [Real.mul_rpow (by positivity) (by positivity)]
    simp [one_div, mul_inv]
    ring

private theorem reciprocalPower_eq_hom (x : ℝ) (n : ℕ) :
    reciprocalPower x n = reciprocalPowerHom x n := rfl

private theorem reciprocalPower_summable (x : ℝ) (hx : 1 < x) :
    Summable (reciprocalPower x) := by
  unfold reciprocalPower
  exact Real.summable_one_div_nat_rpow.mpr hx

private theorem reciprocalPower_prime_lt_one (x : ℝ) (hx : 1 < x)
    {p : ℕ} (hp : p.Prime) : |reciprocalPower x p| < 1 := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hrpow : 1 < Real.rpow (p : ℝ) x := by
    calc
      (1 : ℝ) < (p : ℝ) := hp1
      _ = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ < (p : ℝ) ^ x := Real.rpow_lt_rpow_of_exponent_lt hp1 hx
  unfold reciprocalPower
  change |1 / ((p : ℝ) ^ x)| < 1
  rw [abs_of_pos (one_div_pos.mpr (Real.rpow_pos_of_pos (by positivity) x))]
  exact (div_lt_one (Real.rpow_pos_of_pos (by positivity) x)).2 hrpow

private theorem gap1_proof (x : ℝ) (hx : 1 < x) (p : ℕ) (hp : p.Prime) :
    eulerFactor x p = ∑' k : ℕ, reciprocalPower x (p ^ k) := by
  have hgeom : Summable (fun k : ℕ => (reciprocalPower x p) ^ k) :=
    summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs] using
      (reciprocalPower_prime_lt_one x hx hp))
  calc
    eulerFactor x p = ∑' k : ℕ, (reciprocalPower x p) ^ k := by
      unfold eulerFactor
      exact (hasSum_geometric_of_norm_lt_one (by
        simpa [Real.norm_eq_abs] using
          (reciprocalPower_prime_lt_one x hx hp))).tsum_eq.symm
    _ = ∑' k : ℕ, reciprocalPower x (p ^ k) := by
      apply tsum_congr
      intro k
      change (reciprocalPowerHom x p) ^ k = reciprocalPowerHom x (p ^ k)
      exact ((reciprocalPowerHom x).map_pow p k).symm

private theorem smooth_iff (N n : ℕ) :
    IsSmoothUpTo N n ↔ n ∈ Nat.smoothNumbers (N + 1) := by
  rw [Nat.mem_smoothNumbers']
  unfold IsSmoothUpTo
  constructor
  · intro h p hp hd
    exact Nat.lt_succ_iff.mpr (h p hp hd)
  · intro h p hp hd
    exact Nat.lt_succ_iff.mp (h p hp hd)

private theorem primesUpTo_eq (N : ℕ) :
    primesUpTo N = (N + 1).primesBelow := by
  ext p
  simp [primesUpTo, Nat.mem_primesBelow, Nat.lt_succ_iff, and_comm]

private theorem gap2_proof (x : ℝ) (hx : 1 < x) (N : ℕ) :
    eulerPartialProduct x N = smoothSeries x N := by
  let f : ℕ →* ℝ := reciprocalPowerHom x
  let S : Set ℕ := Nat.smoothNumbers (N + 1)
  let g : ℕ → ℝ := S.indicator f
  have hEuler :=
    EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers
      (f := f) (reciprocalPower_summable x hx) (N + 1)
  rw [tsum_subtype] at hEuler
  have hg : Summable g := by
    exact (reciprocalPower_summable x hx).indicator S
  have hsplit := hg.sum_add_tsum_nat_add 1
  have hg0 : g 0 = 0 := by
    simp [g, S, Nat.smoothNumbers]
  have hshift : (∑' k : ℕ, g k) = ∑' k : ℕ, g (k + 1) := by
    simpa [hg0] using hsplit.symm
  calc
    eulerPartialProduct x N = ∑' n : ℕ, g n := by
      simpa [eulerPartialProduct, eulerFactor, primesUpTo_eq,
        reciprocalPower_eq_hom, f, g, S] using hEuler
    _ = ∑' k : ℕ, g (k + 1) := hshift
    _ = smoothSeries x N := by
      unfold smoothSeries
      apply tsum_congr
      intro k
      simp only [g, S, Set.indicator_apply]
      by_cases h : IsSmoothUpTo N (k + 1)
      · have hs : k + 1 ∈ Nat.smoothNumbers (N + 1) :=
          (smooth_iff N (k + 1)).1 h
        simp [h, hs, f, reciprocalPower_eq_hom]
      · have hs : k + 1 ∉ Nat.smoothNumbers (N + 1) := by
          intro hs
          exact h ((smooth_iff N (k + 1)).2 hs)
        simp [h, hs]

private theorem gap3_proof :
    ∀ N n : ℕ, 1 ≤ n → n ≤ N → IsSmoothUpTo N n := by
  intro N n hn hN p hp hd
  exact (Nat.le_of_dvd (by omega) hd).trans hN

private theorem reciprocalPower_nonneg (x : ℝ) (n : ℕ) :
    0 ≤ reciprocalPower x n := by
  unfold reciprocalPower
  change 0 ≤ 1 / ((n : ℝ) ^ x)
  exact one_div_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) x)

private theorem seriesTerm_summable (x : ℝ) (hx : 1 < x) :
    Summable (fun k : ℕ => reciprocalPower x (k + 1)) :=
  (reciprocalPower_summable x hx).comp_injective Nat.succ_injective

private theorem gap4_proof (x : ℝ) (hx : 1 < x) :
    ∀ N, |zetaSeries x - eulerPartialProduct x N| ≤ tailSeries x N := by
  intro N
  let t : ℕ → ℝ := fun k => reciprocalPower x (k + 1)
  let s : ℕ → ℝ := fun k =>
    if IsSmoothUpTo N (k + 1) then reciprocalPower x (k + 1) else 0
  have ht : Summable t := seriesTerm_summable x hx
  have hs : Summable s := by
    have hi := ht.indicator {k : ℕ | IsSmoothUpTo N (k + 1)}
    simpa only [t, s, Set.indicator_apply, Set.mem_setOf_eq] using hi
  have ht0 : ∀ k, 0 ≤ t k := fun k => reciprocalPower_nonneg x (k + 1)
  have hs0 : ∀ k, 0 ≤ s k := by
    intro k
    unfold s
    split_ifs
    · exact reciprocalPower_nonneg x (k + 1)
    · norm_num
  have hst : ∀ k, s k ≤ t k := by
    intro k
    unfold s t
    split_ifs <;> simp [reciprocalPower_nonneg]
  have hs_le : (∑' k, s k) ≤ ∑' k, t k :=
    hs.tsum_le_tsum hst ht
  have hprefix_eq :
      (∑ k ∈ Finset.range N, t k) = ∑ k ∈ Finset.range N, s k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < N := Finset.mem_range.mp hk
    have hkN : k + 1 ≤ N := by omega
    have hsm : IsSmoothUpTo N (k + 1) := gap3_proof N (k + 1) (by omega) hkN
    simp [s, t, hsm]
  have hprefix_le : (∑ k ∈ Finset.range N, t k) ≤ ∑' k, s k := by
    rw [hprefix_eq]
    exact hs.sum_le_tsum (Finset.range N) (fun k hk => hs0 k)
  have hsplit := ht.sum_add_tsum_nat_add N
  have htail :
      (∑' k, t k) - (∑ k ∈ Finset.range N, t k) = tailSeries x N := by
    unfold tailSeries
    rw [← hsplit]
    ring_nf
    apply tsum_congr
    intro k
    unfold t
    congr 1
    omega
  rw [gap2_proof x hx N]
  unfold zetaSeries smoothSeries
  change |(∑' k, t k) - ∑' k, s k| ≤ tailSeries x N
  rw [abs_of_nonneg (sub_nonneg.mpr hs_le)]
  calc
    (∑' k, t k) - ∑' k, s k ≤
        (∑' k, t k) - ∑ k ∈ Finset.range N, t k :=
      sub_le_sub_left hprefix_le _
    _ = tailSeries x N := htail

private theorem tailSeries_tendsto_zero (x : ℝ) (hx : 1 < x) :
    Tendsto (tailSeries x) atTop (𝓝 0) := by
  have hs : Summable (reciprocalPower x) := reciprocalPower_summable x hx
  have hpref := hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto
      (fun N : ℕ => (∑' n : ℕ, reciprocalPower x n) -
        ∑ n ∈ Finset.range (N + 1), reciprocalPower x n)
      atTop (𝓝 0) := by
    have hconst : Tendsto
        (fun _ : ℕ => ∑' n : ℕ, reciprocalPower x n) atTop
        (𝓝 (∑' n : ℕ, reciprocalPower x n)) := tendsto_const_nhds
    simpa using hconst.sub hpref
  apply hdiff.congr'
  filter_upwards with N
  have hsplit := hs.sum_add_tsum_nat_add (N + 1)
  unfold tailSeries
  rw [← hsplit]
  ring_nf

private theorem gap5_proof (x : ℝ) (hx : 1 < x) :
    Tendsto
      (fun N => |zetaSeries x - eulerPartialProduct x N|)
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun N => abs_nonneg _
  · exact Eventually.of_forall fun N => gap4_proof x hx N
  · exact tailSeries_tendsto_zero x hx

private theorem gap6_proof (x : ℝ) (hx : 1 < x) :
    Tendsto (eulerPartialProduct x) atTop (𝓝 (zetaSeries x)) := by
  have h := gap5_proof x hx
  rw [Metric.tendsto_atTop] at h ⊢
  simpa [Real.dist_eq, abs_sub_comm] using h

private theorem gap7_proof (x : ℝ) (hx : 1 < x) :
    Tendsto (eulerPartialProduct x) atTop (𝓝 (zetaSeries x)) := by
  exact gap6_proof x hx

/--
Source: `proof_gap/exercise_3100/1.txt`; add the missing constant term and
replace the ellipsis by an exact geometric tsum.
-/
theorem gap1 (x : ℝ) (hx : 1 < x) (p : ℕ) (hp : p.Prime) :
    eulerFactor x p =
      ∑' k : ℕ, reciprocalPower x (p ^ k) := by
  exact gap1_proof x hx p hp

/--
Source: `proof_gap/exercise_3100/2.txt`; use the complete finite set of
primes up to `N` and the exact smooth-number expansion.
-/
theorem gap2 (x : ℝ) (hx : 1 < x) (N : ℕ) :
    eulerPartialProduct x N = smoothSeries x N := by
  exact gap2_proof x hx N

/-- Source: `proof_gap/exercise_3100/3.txt`; state the finite-set inclusion exactly. -/
theorem gap3 :
    ∀ N n : ℕ, 1 ≤ n → n ≤ N → IsSmoothUpTo N n := by
  exact gap3_proof

/-- Source: `proof_gap/exercise_3100/4.txt`; replace the tail ellipsis by a tsum. -/
theorem gap4 (x : ℝ) (hx : 1 < x) :
    ∀ N,
      |zetaSeries x - eulerPartialProduct x N| ≤ tailSeries x N := by
  exact gap4_proof x hx

/-- Source: `proof_gap/exercise_3100/5.txt`. -/
theorem gap5 (x : ℝ) (hx : 1 < x) :
    Tendsto
      (fun N => |zetaSeries x - eulerPartialProduct x N|)
      atTop (𝓝 0) := by
  exact gap5_proof x hx

/-- Source: `proof_gap/exercise_3100/6.txt`; state the infinite product by its cutoffs. -/
theorem gap6 (x : ℝ) (hx : 1 < x) :
    Tendsto (eulerPartialProduct x) atTop (𝓝 (zetaSeries x)) := by
  exact gap6_proof x hx

/-- Source: `proof_gap/exercise_3100/7.txt`. -/
theorem gap7 (x : ℝ) (hx : 1 < x) :
    Tendsto (eulerPartialProduct x) atTop (𝓝 (zetaSeries x)) := by
  exact gap7_proof x hx

end

end ProofGap.Exercise3100
