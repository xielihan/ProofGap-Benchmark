import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2586

noncomputable section

def nthRoot (n : ℕ) (x : ℝ) : ℝ :=
  Real.rpow x (1 / (n : ℝ))

def targetTerm (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 / (2 + 1 / (n : ℝ)) ^ n

def rootTerm (n : ℕ) : ℝ := nthRoot n (targetTerm n)

def comparisonTerm (n : ℕ) : ℝ :=
  nthRoot n n * nthRoot n n / (2 + 1 / (n : ℝ))

private theorem targetTerm_pos {n : ℕ} (hn : 0 < n) :
    0 < targetTerm n := by
  unfold targetTerm
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hd : 0 < (2 : ℝ) + 1 / (n : ℝ) := by positivity
  positivity

private theorem rootTerm_eq_comparisonTerm_eventually :
    rootTerm =ᶠ[atTop] comparisonTerm := by
  refine Filter.eventually_atTop.2 ⟨1, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hn0 : n ≠ 0 := Nat.ne_of_gt hnpos
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hnR
  have hd : 0 ≤ (2 : ℝ) + (n : ℝ)⁻¹ := by positivity
  unfold rootTerm comparisonTerm nthRoot targetTerm
  simp only [one_div]
  have hdiv :
      ((n : ℝ) ^ 2 / (2 + (n : ℝ)⁻¹) ^ n).rpow ((n : ℝ)⁻¹) =
        ((n : ℝ) ^ 2).rpow ((n : ℝ)⁻¹) /
          ((2 + (n : ℝ)⁻¹) ^ n).rpow ((n : ℝ)⁻¹) := by
    simpa only using
      (Real.div_rpow (sq_nonneg (n : ℝ)) (pow_nonneg hd n)
        ((n : ℝ)⁻¹))
  have hsq :
      ((n : ℝ) ^ 2).rpow ((n : ℝ)⁻¹) =
        (n : ℝ).rpow ((n : ℝ)⁻¹) *
          (n : ℝ).rpow ((n : ℝ)⁻¹) := by
    rw [pow_two]
    exact Real.mul_rpow hnnonneg hnnonneg
  have hden :
      ((2 + (n : ℝ)⁻¹) ^ n).rpow ((n : ℝ)⁻¹) =
        2 + (n : ℝ)⁻¹ := by
    simpa only using (Real.pow_rpow_inv_natCast hd hn0)
  calc
    ((n : ℝ) ^ 2 / (2 + (n : ℝ)⁻¹) ^ n).rpow ((n : ℝ)⁻¹) =
        ((n : ℝ) ^ 2).rpow ((n : ℝ)⁻¹) /
          ((2 + (n : ℝ)⁻¹) ^ n).rpow ((n : ℝ)⁻¹) := hdiv
    _ = ((n : ℝ).rpow ((n : ℝ)⁻¹) *
          (n : ℝ).rpow ((n : ℝ)⁻¹)) /
          ((2 + (n : ℝ)⁻¹) ^ n).rpow ((n : ℝ)⁻¹) := by
      rw [hsq]
    _ = (n : ℝ).rpow ((n : ℝ)⁻¹) * (n : ℝ).rpow ((n : ℝ)⁻¹) /
          (2 + (n : ℝ)⁻¹) := by
      rw [hden]

private theorem tendsto_nthRoot_nat :
    Tendsto (fun n : ℕ => nthRoot n (n : ℝ)) atTop (nhds 1) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlogReal :
      Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlog :
      Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    hlogReal.comp hcast
  have hexp :
      Tendsto (fun n : ℕ => Real.exp (Real.log (n : ℝ) / (n : ℝ)))
        atTop (nhds 1) := by
    simpa using Real.continuous_exp.continuousAt.tendsto.comp hlog
  have heq :
      (fun n : ℕ => nthRoot n (n : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => Real.exp (Real.log (n : ℝ) / (n : ℝ))) := by
    refine Filter.eventually_atTop.2 ⟨1, ?_⟩
    intro n hn
    have hnpos : 0 < n := by omega
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    change (n : ℝ).rpow (1 / (n : ℝ)) =
      Real.exp (Real.log (n : ℝ) / (n : ℝ))
    simpa [div_eq_mul_inv] using
      (Real.rpow_def_of_pos hnR (1 / (n : ℝ)))
  exact hexp.congr' heq.symm

private theorem targetTerm_eq_rootTerm_pow {n : ℕ} (hn : 0 < n) :
    targetTerm n = (rootTerm n) ^ n := by
  have ht := targetTerm_pos hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0R : (n : ℝ) ≠ 0 := ne_of_gt hnR
  unfold rootTerm nthRoot
  have hrpow :
      (targetTerm n).rpow (1 / (n : ℝ)) =
        Real.exp (Real.log (targetTerm n) * (1 / (n : ℝ))) :=
    Real.rpow_def_of_pos ht (1 / (n : ℝ))
  rw [hrpow, ← Real.exp_nat_mul]
  have hexp :
      (n : ℝ) * (Real.log (targetTerm n) * (1 / (n : ℝ))) =
        Real.log (targetTerm n) := by
    field_simp [hn0R]
  rw [hexp, Real.exp_log ht]

theorem gap1
    (a : ℕ → ℝ) (ha : ∀ n, a n = targetTerm n) :
    ∀ L : ℝ, Tendsto (fun n => nthRoot n (a n)) atTop (nhds L) ↔
      Tendsto rootTerm atTop (nhds L) := by
  intro L
  have heq : (fun n => nthRoot n (a n)) = rootTerm := by
    funext n
    rw [ha n]
    rfl
  rw [heq]

theorem gap2 :
    ∀ L : ℝ, Tendsto rootTerm atTop (nhds L) ↔
      Tendsto comparisonTerm atTop (nhds L) := by
  intro L
  constructor
  · intro h
    exact h.congr' rootTerm_eq_comparisonTerm_eventually
  · intro h
    exact h.congr' rootTerm_eq_comparisonTerm_eventually.symm

theorem gap3 :
    Tendsto comparisonTerm atTop (nhds (1 / 2 : ℝ)) := by
  change Tendsto
    (fun n : ℕ => nthRoot n (n : ℝ) * nthRoot n (n : ℝ) /
      (2 + 1 / (n : ℝ))) atTop (nhds (1 / 2 : ℝ))
  have hroot := tendsto_nthRoot_nat
  have hnum :
      Tendsto (fun n : ℕ => nthRoot n (n : ℝ) * nthRoot n (n : ℝ))
        atTop (nhds 1) := by
    simpa only [one_mul] using hroot.mul hroot
  have hinv :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  have hden :
      Tendsto (fun n : ℕ => (2 : ℝ) + 1 / (n : ℝ)) atTop (nhds 2) := by
    simpa only [add_zero] using tendsto_const_nhds.add hinv
  exact hnum.div hden (by norm_num)

theorem gap4 :
    (1 / 2 : ℝ) < 1 := by
  norm_num

theorem gap5
    (a : ℕ → ℝ) (ha : ∀ n, a n = targetTerm n)
    (haRoot : ∀ L : ℝ,
      Tendsto (fun n => nthRoot n (a n)) atTop (nhds L) ↔
        Tendsto rootTerm atTop (nhds L))
    (hrootCompare : ∀ L : ℝ, Tendsto rootTerm atTop (nhds L) ↔
      Tendsto comparisonTerm atTop (nhds L))
    (hcomparison : Tendsto comparisonTerm atTop (nhds (1 / 2 : ℝ)))
    (hlt : (1 / 2 : ℝ) < 1) :
    Tendsto (fun n => nthRoot n (a n)) atTop (nhds (1 / 2 : ℝ)) ∧
      (1 / 2 : ℝ) < 1 := by
  constructor
  · exact (haRoot (1 / 2 : ℝ)).2 ((hrootCompare (1 / 2 : ℝ)).2 hcomparison)
  · exact hlt

theorem gap6
    (hroot : Tendsto rootTerm atTop (nhds (1 / 2 : ℝ)))
    (hlt : (1 / 2 : ℝ) < 1) :
    Summable targetTerm := by
  let q : ℝ := 3 / 4
  have hq0 : 0 ≤ q := by
    dsimp [q]
    norm_num
  have hq1 : q < 1 := by
    dsimp [q]
    norm_num
  have hevent : ∀ᶠ n in atTop, rootTerm n < q := by
    exact (tendsto_order.1 hroot).2 q (by dsimp [q]; norm_num)
  have hge : ∀ᶠ n : ℕ in atTop, 1 ≤ n := by
    exact Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩
  have hbound : ∀ᶠ n : ℕ in Filter.cofinite,
      rootTerm n < q ∧ 1 ≤ n := by
    rw [Nat.cofinite_eq_atTop]
    exact hevent.and hge
  have hgeom : Summable (fun n : ℕ => q ^ n) := by
    apply summable_geometric_of_norm_lt_one
    simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  apply hgeom.of_norm_bounded_eventually
  filter_upwards [hbound] with n hn
  have hnpos : 0 < n := by omega
  have htpos := targetTerm_pos hnpos
  have hrnonneg : 0 ≤ rootTerm n := by
    unfold rootTerm nthRoot
    exact Real.rpow_nonneg (le_of_lt htpos) (1 / (n : ℝ))
  have hpow : ∀ k : ℕ, rootTerm n ^ k ≤ q ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, pow_succ]
        exact mul_le_mul ih (le_of_lt hn.1) hrnonneg (pow_nonneg hq0 k)
  calc
    ‖targetTerm n‖ = targetTerm n := by
      rw [Real.norm_eq_abs, abs_of_pos htpos]
    _ = rootTerm n ^ n := targetTerm_eq_rootTerm_pow hnpos
    _ ≤ q ^ n := hpow n

theorem gap7
    (hsum : Summable targetTerm) :
    Summable targetTerm := by
  exact hsum

end

end ProofGap.Exercise2586
