import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise3105_1

noncomputable section

open Filter
open scoped BigOperators Topology

def admissible (x : ℝ) : Prop :=
  ∀ m : ℕ, x ≠ -(m : ℝ)

def eulerApproximant (x : ℝ) (n : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) * Real.rpow n x /
    (x * ∏ k ∈ Finset.Icc 1 n, (x + k))

def productFactor (x : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (1 + 1 / (n : ℝ)) x / (1 + x / n)

def factorPartialProduct (x : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 n, productFactor x k

def HasProductFromOne (x L : ℝ) : Prop :=
  Tendsto (factorPartialProduct x) atTop (𝓝 L)

private lemma admissible_ne_zero {x : ℝ} (hx : admissible x) : x ≠ 0 := by
  simpa using hx 0

private lemma admissible_add_nat_ne_zero {x : ℝ} (hx : admissible x) (k : ℕ) :
    x + k ≠ 0 := by
  intro h
  apply hx k
  linarith

private lemma factorial_eq_prod_Icc_cast (n : ℕ) :
    (Nat.factorial n : ℝ) = ∏ k ∈ Finset.Icc 1 n, (k : ℝ) := by
  rw [← Finset.prod_natCast]
  rw [← Finset.prod_Ico_id_eq_factorial]
  congr 1

private lemma prod_one_add_div (x : ℝ) (n : ℕ) :
    (∏ k ∈ Finset.Icc 1 n, (1 + x / k)) =
      (∏ k ∈ Finset.Icc 1 n, (x + k)) / (Nat.factorial n : ℝ) := by
  rw [factorial_eq_prod_Icc_cast]
  calc
    (∏ k ∈ Finset.Icc 1 n, (1 + x / k)) =
        ∏ k ∈ Finset.Icc 1 n, ((x + k) / k) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hk0 : (k : ℝ) ≠ 0 := by
        have : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        positivity
      field_simp
      ring
    _ = (∏ k ∈ Finset.Icc 1 n, (x + k)) /
        ∏ k ∈ Finset.Icc 1 n, (k : ℝ) := by
      rw [Finset.prod_div_distrib]

private lemma prod_one_add_inv (n : ℕ) :
    (∏ k ∈ Finset.Icc 1 n, (1 + 1 / (k : ℝ))) = n + 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : n + 1 ∉ Finset.Icc 1 n := by
        intro hmem
        have hle := (Finset.mem_Icc.mp hmem).2
        omega
      rw [hIcc, Finset.prod_insert hnot, ih]
      have hnpos : (0 : ℝ) < n + 1 := by positivity
      field_simp
      norm_num [Nat.cast_add, Nat.cast_one]

private lemma prod_rpow_one_add_inv (x : ℝ) (n : ℕ) :
    (∏ k ∈ Finset.Icc 1 n, Real.rpow (1 + 1 / (k : ℝ)) x) =
      Real.rpow (n + 1 : ℕ) x := by
  have hnonneg : ∀ k ∈ Finset.Icc 1 n, (0 : ℝ) ≤ 1 + 1 / (k : ℝ) := by
    intro k hk
    have hkpos : (0 : ℝ) < k := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1)
    positivity
  have h := Real.finset_prod_rpow (Finset.Icc 1 n)
    (fun k : ℕ => 1 + 1 / (k : ℝ)) hnonneg x
  rw [prod_one_add_inv] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

private lemma prod_rpow_div_last (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (∏ k ∈ Finset.Icc 1 n, Real.rpow (1 + 1 / (k : ℝ)) x) /
        Real.rpow (1 + 1 / (n : ℝ)) x =
      Real.rpow n x := by
  rw [prod_rpow_one_add_inv]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1pos : (0 : ℝ) < n + 1 := by positivity
  have hbase : 1 + 1 / (n : ℝ) = ((n : ℝ) + 1) / n := by
    field_simp
  rw [hbase]
  norm_num [Nat.cast_add, Nat.cast_one]
  rw [Real.div_rpow hn1pos.le hnpos.le]
  have hnpow : Real.rpow (n : ℝ) x ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos x).ne'
  have hn1pow : Real.rpow ((n : ℝ) + 1) x ≠ 0 :=
    (Real.rpow_pos_of_pos hn1pos x).ne'
  field_simp

private lemma prod_range_add_eq (x : ℝ) (n : ℕ) :
    (∏ j ∈ Finset.range (n + 1), (x + j)) =
      x * ∏ k ∈ Finset.Icc 1 n, (x + k) := by
  have hset : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hzero : 0 ∉ Finset.Icc 1 n := by simp
  rw [hset, Finset.prod_insert hzero]
  norm_num

private lemma eulerApproximant_eq_GammaSeq (x : ℝ) (n : ℕ) :
    eulerApproximant x n = Real.GammaSeq x n := by
  unfold eulerApproximant Real.GammaSeq
  rw [prod_range_add_eq]
  change (Nat.factorial n : ℝ) * Real.rpow (n : ℝ) x /
      (x * ∏ k ∈ Finset.Icc 1 n, (x + k)) =
    Real.rpow (n : ℝ) x * (Nat.factorial n : ℝ) /
      (x * ∏ k ∈ Finset.Icc 1 n, (x + k))
  ring

private lemma factorPartialProduct_eq_prod_div (x : ℝ) (n : ℕ) :
    factorPartialProduct x n =
      (∏ k ∈ Finset.Icc 1 n, Real.rpow (1 + 1 / (k : ℝ)) x) /
        (∏ k ∈ Finset.Icc 1 n, (1 + x / k)) := by
  unfold factorPartialProduct productFactor
  rw [Finset.prod_div_distrib]

/--
Source: `proof_gap/exercise_3105_1/1.txt`; exclude the poles and start the
finite product at a positive cutoff.
-/
theorem gap1 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : admissible x) :
    eulerApproximant x n =
      Real.rpow n x / x *
        (1 / ∏ k ∈ Finset.Icc 1 n, (1 + x / k)) := by
  have hx0 := admissible_ne_zero hx
  have hprod0 : (∏ k ∈ Finset.Icc 1 n, (x + k)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact admissible_add_nat_ne_zero hx k
  have hfact0 : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  unfold eulerApproximant
  rw [prod_one_add_div]
  field_simp [hx0, hprod0, hfact0]

/-- Source: `proof_gap/exercise_3105_1/2.txt`; all denominators are nonzero on `admissible x`. -/
theorem gap2 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : admissible x) :
    eulerApproximant x n =
      (1 / x) *
        ((∏ k ∈ Finset.Icc 1 n, Real.rpow (1 + 1 / (k : ℝ)) x) /
          (∏ k ∈ Finset.Icc 1 n, (1 + x / k))) *
        (1 / Real.rpow (1 + 1 / (n : ℝ)) x) := by
  rw [gap1 n x hn hx]
  have hx0 := admissible_ne_zero hx
  have hden0 : (∏ k ∈ Finset.Icc 1 n, (1 + x / k)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    have hk0 : (k : ℝ) ≠ 0 := by
      have : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      positivity
    have hxk0 := admissible_add_nat_ne_zero hx k
    rw [show 1 + x / (k : ℝ) = (x + k) / k by
      field_simp [hk0]
      ring]
    exact div_ne_zero hxk0 hk0
  have hlast0 : Real.rpow (1 + 1 / (n : ℝ)) x ≠ 0 := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hbase : 0 < 1 + 1 / (n : ℝ) := by positivity
    exact (Real.rpow_pos_of_pos hbase x).ne'
  have hprod := prod_rpow_div_last x n hn
  field_simp [hx0, hden0, hlast0] at hprod ⊢
  nlinarith

private lemma factorPartialProduct_eq_euler_mul (x : ℝ) (n : ℕ)
    (hn : 1 ≤ n) (hx : admissible x) :
    factorPartialProduct x n =
      x * eulerApproximant x n * Real.rpow (1 + 1 / (n : ℝ)) x := by
  have h := gap2 n x hn hx
  rw [← factorPartialProduct_eq_prod_div] at h
  have hx0 := admissible_ne_zero hx
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbase : 0 < 1 + 1 / (n : ℝ) := by positivity
  have hr0 : Real.rpow (1 + 1 / (n : ℝ)) x ≠ 0 :=
    (Real.rpow_pos_of_pos hbase x).ne'
  have hrewrite : 1 + 1 / (n : ℝ) = ((n : ℝ) + 1) / n := by
    field_simp
  rw [hrewrite] at h hr0 ⊢
  field_simp [hx0, hr0] at h
  calc
    factorPartialProduct x n =
        eulerApproximant x n * x * Real.rpow (((n : ℝ) + 1) / n) x := h.symm
    _ = x * eulerApproximant x n * Real.rpow (((n : ℝ) + 1) / n) x := by ring

/--
Source: `proof_gap/exercise_3105_1/3.txt`; the infinite product is represented
by convergence of its partial products.
-/
theorem gap3 (Gamma : ℝ → ℝ)
    (hGamma :
      ∀ x : ℝ, admissible x →
        Tendsto (eulerApproximant x) atTop (𝓝 (Gamma x))) :
    ∀ x : ℝ, admissible x →
      ∃ L : ℝ,
        L ≠ 0 ∧
        HasProductFromOne x L ∧
        Gamma x = (1 / x) * L := by
  intro x hx
  have hx0 := admissible_ne_zero hx
  have hEulerReal : Tendsto (eulerApproximant x) atTop (𝓝 (Real.Gamma x)) := by
    apply (Real.GammaSeq_tendsto_Gamma x).congr'
    exact Eventually.of_forall fun n => (eulerApproximant_eq_GammaSeq x n).symm
  have hGammaEq : Gamma x = Real.Gamma x :=
    tendsto_nhds_unique (hGamma x hx) hEulerReal
  have hGamma0 : Gamma x ≠ 0 := by
    rw [hGammaEq]
    exact Real.Gamma_ne_zero hx
  refine ⟨x * Gamma x, mul_ne_zero hx0 hGamma0, ?_, ?_⟩
  · unfold HasProductFromOne
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero.comp hnat
    have hbase : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hinv
    have hrpow : Tendsto
        (fun n : ℕ => Real.rpow (1 + 1 / (n : ℝ)) x) atTop (𝓝 1) := by
      simpa using
        (Real.continuousAt_rpow_const 1 x (Or.inl one_ne_zero)).tendsto.comp hbase
    have hmodel : Tendsto
        (fun n : ℕ => x * eulerApproximant x n *
          Real.rpow (1 + 1 / (n : ℝ)) x) atTop (𝓝 (x * Gamma x)) := by
      convert (tendsto_const_nhds.mul (hGamma x hx)).mul hrpow using 1 <;> ring
    apply hmodel.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact (factorPartialProduct_eq_euler_mul x n hn hx).symm
  · field_simp

end

end ProofGap.Exercise3105_1
