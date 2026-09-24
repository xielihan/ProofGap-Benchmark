import ProofGapLean.Prelude.Analysis
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.SumPrimeReciprocals

namespace ProofGap.Exercise3101

noncomputable section

open Filter
open scoped BigOperators Topology

def primesUpTo (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter Nat.Prime

def harmonicPartialSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)

def reciprocalEulerPartialProduct (N : ℕ) : ℝ :=
  ∏ p ∈ primesUpTo N, (1 / (1 - 1 / (p : ℝ)))

def primeDeficitProduct (N : ℕ) : ℝ :=
  ∏ p ∈ primesUpTo N, (1 - 1 / (p : ℝ))

def primeReciprocalPartialSum (N : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo N, 1 / (p : ℝ)

private theorem primesUpTo_eq (N : ℕ) :
    primesUpTo N = (N + 1).primesBelow := by
  ext p
  simp [primesUpTo, Nat.mem_primesBelow]

private theorem harmonic_eq (N : ℕ) :
    harmonicPartialSum N = (harmonic N : ℝ) := by
  unfold harmonicPartialSum
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast, one_div]

private def reciprocal (n : ℕ) : ℝ := 1 / (n : ℝ)

private theorem reciprocal_one : reciprocal 1 = 1 := by
  simp [reciprocal]

private theorem reciprocal_mul (m n : ℕ) :
    reciprocal (m * n) = reciprocal m * reciprocal n := by
  unfold reciprocal
  push_cast
  ring

private theorem prime_ratio_norm_lt_one {p : ℕ} (hp : p.Prime) :
    ‖(1 / (p : ℝ) : ℝ)‖ < 1 := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hp0)]
  exact (div_lt_one hp0).2 (by exact_mod_cast hp.one_lt)

private theorem prime_power_summable {p : ℕ} (hp : p.Prime) :
    Summable (fun e : ℕ => ‖reciprocal (p ^ e)‖) := by
  have hgeom :
      Summable (fun e : ℕ => (1 / (p : ℝ) : ℝ) ^ e) :=
    summable_geometric_of_norm_lt_one (prime_ratio_norm_lt_one hp)
  apply hgeom.congr
  intro e
  simp [reciprocal, norm_pow]

private theorem prime_geometric_sum {p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, reciprocal (p ^ e)) =
      1 / (1 - 1 / (p : ℝ)) := by
  have hgeom :=
    hasSum_geometric_of_norm_lt_one (prime_ratio_norm_lt_one hp)
  calc
    (∑' e : ℕ, reciprocal (p ^ e)) =
        ∑' e : ℕ, (1 / (p : ℝ)) ^ e := by
          apply tsum_congr
          intro e
          simp [reciprocal]
    _ = 1 / (1 - 1 / (p : ℝ)) := by
      simpa [one_div] using hgeom.tsum_eq

private theorem euler_hasSum (N : ℕ) :
    HasSum
      (fun m : (N + 1).smoothNumbers => reciprocal m)
      (reciprocalEulerPartialProduct N) := by
  have hEuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      reciprocal_one
      (fun {m n} _ => reciprocal_mul m n)
      (fun {_} hp => prime_power_summable hp)
      (N + 1)
  unfold reciprocalEulerPartialProduct
  rw [primesUpTo_eq]
  convert hEuler.2 using 1
  apply Finset.prod_congr rfl
  intro p hp
  exact (prime_geometric_sum (Nat.prime_of_mem_primesBelow hp)).symm

private theorem harmonic_lt_euler (N : ℕ) (hN : 2 ≤ N) :
    harmonicPartialSum N < reciprocalEulerPartialProduct N := by
  classical
  let S : Set ℕ := (N + 1).smoothNumbers
  let I : Finset ℕ := Finset.Icc 1 N
  have hI_smooth {n : ℕ} (hn : n ∈ I) : n ∈ S := by
    have hnI : n ∈ Finset.Icc 1 N := hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
    have hnN : n ≤ N := (Finset.mem_Icc.mp hnI).2
    have hnpos : 0 < n := by omega
    have hnlt : n < N + 1 := by omega
    exact Nat.mem_smoothNumbers_of_lt hnpos hnlt
  let e : {n // n ∈ I} ↪ {n // n ∈ S} :=
    ⟨fun n => ⟨n, hI_smooth n.property⟩,
      fun a b hab => Subtype.ext
        (show (a : ℕ) = (b : ℕ) from
          congrArg (fun z : {n // n ∈ S} => z.val) hab)⟩
  let T : Finset {n // n ∈ S} := I.attach.map e
  let f : {n // n ∈ S} → ℝ := fun m => reciprocal m
  let g : {n // n ∈ S} → ℝ :=
    fun m => if m.val ∈ I then reciprocal m else 0
  have hsumf : Summable f := by
    exact (euler_hasSum N).summable
  have hgf : ∀ m, g m ≤ f m := by
    intro m
    by_cases hm : m.val ∈ I
    · simp [g, f, hm]
    · simp [g, f, hm, reciprocal]
  have hg0 : ∀ m, 0 ≤ g m := by
    intro m
    by_cases hm : m.val ∈ I <;> simp [g, hm, reciprocal]
  have hsumg : Summable g :=
    Summable.of_nonneg_of_le hg0 hgf hsumf
  have houtside_smooth : 2 ^ N ∈ S := by
    have hone : 1 ∈ Nat.smoothNumbers 2 :=
      Nat.mem_smoothNumbers_of_lt (by norm_num) (by norm_num)
    have hpow : 2 ^ N * 1 ∈ Nat.smoothNumbers 3 :=
      Nat.pow_mul_mem_smoothNumbers (by norm_num) N hone
    change 2 ^ N ∈ (N + 1).smoothNumbers
    exact Nat.smoothNumbers_mono (show 3 ≤ N + 1 by omega) (by simpa using hpow)
  let m₀ : {n // n ∈ S} := ⟨2 ^ N, houtside_smooth⟩
  have hm₀gt : N < m₀.val := by
    dsimp [m₀]
    exact N.lt_two_pow_self
  have hstrict : g m₀ < f m₀ := by
    have hm₀I : m₀.val ∉ I := by
      intro hm
      exact (not_le_of_gt hm₀gt) (Finset.mem_Icc.mp hm).2
    simp only [g, f, if_neg hm₀I]
    unfold reciprocal
    positivity
  have hlt : (∑' m, g m) < ∑' m, f m :=
    hsumg.tsum_lt_tsum hgf hstrict hsumf
  have hg_support : ∀ m ∉ T, g m = 0 := by
    intro m hmT
    by_cases hmI : m.val ∈ I
    · have hmT' : m ∈ T := by
        simp only [T, Finset.mem_map, Finset.mem_attach]
        exact ⟨⟨m.val, hmI⟩, trivial, by
          apply Subtype.ext
          rfl⟩
      exact (hmT hmT').elim
    · simp [g, hmI]
  have hg_tsum : (∑' m, g m) = harmonicPartialSum N := by
    rw [tsum_eq_sum (s := T) hg_support]
    simp [T, e, g, I, reciprocal, harmonicPartialSum]
    calc
      (∑ x ∈ (Finset.Icc 1 N).attach,
          if 1 ≤ x.val ∧ x.val ≤ N then ((x.val : ℕ) : ℝ)⁻¹ else 0) =
          ∑ x ∈ (Finset.Icc 1 N).attach, ((x.val : ℕ) : ℝ)⁻¹ := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [if_pos (Finset.mem_Icc.mp x.property)]
      _ = ∑ x ∈ Finset.Icc 1 N, (x : ℝ)⁻¹ := by
          simpa using
            (Finset.sum_attach (Finset.Icc 1 N)
              (fun x : ℕ => (x : ℝ)⁻¹))
  have hf_tsum : (∑' m, f m) = reciprocalEulerPartialProduct N := by
    exact (euler_hasSum N).tsum_eq
  rw [hg_tsum, hf_tsum] at hlt
  exact hlt

private theorem harmonic_tendsto :
    Tendsto harmonicPartialSum atTop atTop := by
  have hcast :
      Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlog :
      Tendsto (fun N : ℕ => Real.log (((N + 1 : ℕ) : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  refine tendsto_atTop_mono' atTop (Eventually.of_forall ?_) hlog
  intro N
  rw [harmonic_eq]
  exact log_add_one_le_harmonic N

private theorem euler_product_tendsto :
    Tendsto reciprocalEulerPartialProduct atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ harmonic_tendsto
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact (harmonic_lt_euler N hN).le

private theorem prime_sum_tendsto :
    Tendsto primeReciprocalPartialSum atTop atTop := by
  let f : ℕ → ℝ :=
    Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => 1 / (n : ℝ))
  have hf0 : ∀ n, 0 ≤ f n := by
    intro n
    by_cases hn : n.Prime <;> simp [f, hn]
  have hdiv :
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, f n) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hf0).1
      not_summable_one_div_on_primes
  have hshift :=
    hdiv.comp (tendsto_add_atTop_nat 1)
  apply hshift.congr'
  filter_upwards with N
  unfold primeReciprocalPartialSum
  rw [primesUpTo_eq]
  simp only [Nat.primesBelow, Finset.sum_filter, f, Set.indicator_apply,
    Set.mem_setOf_eq]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.mem_range] at hp
  by_cases hprime : p.Prime <;> simp [hprime]

private theorem deficit_tendsto :
    Tendsto primeDeficitProduct atTop (𝓝 0) := by
  have hinv :
      Tendsto (fun N => (reciprocalEulerPartialProduct N)⁻¹)
        atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp euler_product_tendsto
  apply hinv.congr'
  filter_upwards with N
  unfold primeDeficitProduct reciprocalEulerPartialProduct
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  simp only [one_div, inv_inv]

/-- Source: `proof_gap/exercise_3101/1.txt`; strictness starts at `N = 2`. -/
theorem gap1 :
    ∀ N : ℕ, 2 ≤ N →
      harmonicPartialSum N < reciprocalEulerPartialProduct N := by
  exact harmonic_lt_euler

/-- Source: `proof_gap/exercise_3101/2.txt`; `+∞` is the filter `atTop`. -/
theorem gap2 :
    Tendsto harmonicPartialSum atTop atTop := by
  exact harmonic_tendsto

/-- Source: `proof_gap/exercise_3101/3.txt`; use the complete prime cutoff. -/
theorem gap3 :
    Tendsto reciprocalEulerPartialProduct atTop atTop := by
  exact euler_product_tendsto

/--
Source: `proof_gap/exercise_3101/4.txt`; use the reciprocal product with the
same prime-by-value cutoff as the preceding step.
-/
theorem gap4 :
    Tendsto primeDeficitProduct atTop (𝓝 0) := by
  exact deficit_tendsto

/-- Source: `proof_gap/exercise_3101/5.txt`; state divergence over all primes by cutoff. -/
theorem gap5 :
    Tendsto primeReciprocalPartialSum atTop atTop := by
  exact prime_sum_tendsto

/-- Source: `proof_gap/exercise_3101/6.txt`. -/
theorem gap6 :
    Tendsto primeReciprocalPartialSum atTop atTop ∧
      Tendsto reciprocalEulerPartialProduct atTop atTop := by
  exact ⟨prime_sum_tendsto, euler_product_tendsto⟩

end

end ProofGap.Exercise3101
